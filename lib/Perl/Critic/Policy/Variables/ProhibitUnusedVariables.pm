##############################################################################
#      $URL$
#     $Date$
#   $Author$
# $Revision$
##############################################################################

package Perl::Critic::Policy::Variables::ProhibitUnusedVariables;

use 5.006001;
use strict;
use warnings;

use Readonly;
use Scalar::Util qw{ refaddr };

use PPI::Token::Symbol;

use Perl::Critic::Utils qw< :booleans :characters hashify :severities >;
use Perl::Critic::Utils::Scope;

use base 'Perl::Critic::Policy';

our $VERSION = '1.112_001';

#-----------------------------------------------------------------------------

Readonly::Scalar my $EXPL =>
    q<Unused variables clutter code and make it harder to read>;

# Determine whether a PPI::Statement::Variable refers to a global or a
# lexical variable. We need to track globals to avoid false negatives
# from things like
#
# my $foo;
# {
#     our $foo;
#     $foo = 'bar';
# }
#
# but we do not need to track 'local', because if you
# s/ \b our \b /local/smxg
# in the above, Perl complains that you can not localize a lexical
# variable, rather than localizing the corresponding global variable.
Readonly::Hash my %GLOBAL_DECLARATION => (
    my  => $FALSE,
    our => $TRUE,
);

# Contents of regular expression to find interpolations. It captures:
# $1 = the sigil ( '$' or '@' ), with leading cast if any
# $2 = the variable (\w+, since we are not worried about built-ins)
# $3 = the first character of the subscript ( '[' or '{' ), if any
Readonly::Scalar my $FIND_INTERPOLATION => <<'EOD';
    (?: \A | .*? (?<! [\\] ) ) (?: \\\\ )*
    ( [\$\@]{1,2} ) ( \w+ | [{] \w+ [}] ) ( [[{]? )
EOD

Readonly::Scalar my $LAST_CHARACTER => -1;

#-----------------------------------------------------------------------------

sub supported_parameters { return (
        {
            name    => 'allow_if_computed_by',
            description => 'Allow if computed by one of these',
            behavior    => 'string list',
        },
        {   name        => 'prohibit_reference_only_variables',
            description => 'Prohibit reference-only variables',
            behavior    => 'boolean',
            default_string  => '0',
        },
        {   name        => 'prohibit_unused_subroutine_arguments',
            description => 'Prohibit unused subroutine arguments',
            behavior    => 'boolean',
            default_string  => '0',
        },
    ) }
sub default_severity     { return $SEVERITY_MEDIUM       }
sub default_themes       { return qw< core maintenance > }
sub applies_to           { return qw< PPI::Document >    }

#-----------------------------------------------------------------------------

sub violates {
    my ( $self, $elem, $document ) = @_;

    my %is_declaration; # Keyed by refaddr of PPI::Token::Symbol. True
                        # if the object represents a declaration.
    my %declared;       # Keyed by PPI::Token::Symbol->symbol(). Values
                        # Are a list of hashes representing declarations
                        # of the given symbol, in reverse order. In each
                        # hash:
                        # {element} is the PPI::Token::Symbol
                        # {is_allowed_computation} is true if the value
                        #     of the symbol is initialized using one of
                        #     the allowed subroutines or classes (e.g.
                        #     Scope::Guard).
                        # {is_global} is true if the declaration is a
                        #     global (i.e. is 'our', not 'my');
                        # {is_unpacking} is true if the declaration
                        #     occurs in an argument unpacking;
                        # {scope} is the scope object for the
                        #     declaration;
                        # {taking_reference} is true if the code takes a
                        #     reference to the declared variable;
                        # {used} is a count of the number of times that
                        #     declaration was used, initialized to 0.

    $self->_get_symbol_declarations(
        $document, \%declared, \%is_declaration );

    _get_symbol_uses( $document, undef, \%declared, \%is_declaration );

    _get_regexp_symbol_uses( $document, \%declared, \%is_declaration );

    _get_double_quotish_string_uses( $document, undef, \%declared );

    _get_here_document_uses( $document, \%declared );

    return $self->_get_violations( \%declared );

}

#-----------------------------------------------------------------------------

sub _get_symbol_declarations {
    my ( $self, $document, $declared, $is_declaration ) = @_;

    foreach my $declaration ( @{ $document->find( 'PPI::Statement::Variable' )
        || [] } ) {

        defined( my $is_global = $GLOBAL_DECLARATION{
            $declaration->type() } )
            or next;

        my ( $assign, $is_allowed_computation, $is_unpacking );
        foreach my $operator ( @{ $declaration->find( 'PPI::Token::Operator' )
            || [] } ) {
            q<=> eq $operator->content()
                or next;
            $assign = $operator;
            my $content = $declaration->content();
            $is_unpacking = $content =~ m<
                = \s* (?: \@_ |
                    shift (?: \s* \@_ )? ) |
                    \$_ [[] .*? []]
                \s* ;? \z >smx;
            $is_allowed_computation = $self->_is_allowed_computation(
                $operator );
            last;
        }

        my $scope = Perl::Critic::Utils::Scope->new( $declaration );

        my $first_operand = $declaration->schild( 1 );

        # We can't just look for symbols, since PPI parses the parens in
        # open( my $fh, '>&', \*STDOUT )
        # as a PPI::Statement::Variable, and we get a false positive on
        # STDOUT.
        my @symbol_list;
        if ( $first_operand->isa( 'PPI::Token::Symbol' ) ) {
            push @symbol_list, $first_operand;
        } elsif ( $first_operand->isa( 'PPI::Structure::List' ) ) {
            push @symbol_list, @{
                $first_operand->find( 'PPI::Token::Symbol' ) || [] };
        } else {
            next;
        }

        foreach my $symbol ( @symbol_list ) {

            if ( $assign ) {
                $symbol->line_number() < $assign->line_number()
                    or $symbol->line_number() == $assign->line_number()
                    and $symbol->column_number() < $assign->column_number()
                    or next;
            }

            $is_declaration->{ refaddr( $symbol ) } = 1;

            unshift @{ $declared->{ _get_symbol_name( $symbol ) } ||= [] }, {
                element => $symbol,
                is_allowed_computation => $is_allowed_computation,
                is_global => $is_global,
                is_unpacking => $is_unpacking,
                scope => $scope,
                taking_reference => scalar _taking_reference_of_variable(
                    $declaration ),
                used  => 0,
            };

        }

    }

    return;
}

#-----------------------------------------------------------------------------

sub _is_allowed_computation {
    my ( $self, $elem ) = @_;  # $elem resumed to be '='.
    my $next_sib = $elem->snext_sibling() or return;
    $next_sib->isa( 'PPI::Token::Word' ) or return;
    my $content = $next_sib->content();
    $self->{_allow_if_computed_by}{$content}
        or return;
    return $content;
}

#-----------------------------------------------------------------------------

sub _taking_reference_of_variable {
    my ( $elem ) = @_;  # Expect a PPI::Statement::Variable
    my $parent = $elem->parent()
        or return;
    my $cast;

    if ( $parent->isa( 'PPI::Structure::List' ) ) {

        $cast = $parent->sprevious_sibling()
            or return;

    } elsif ( $parent->isa( 'PPI::Structure::Block' ) ) {

        my $prev = $parent->sprevious_sibling()
            or return;

        $prev->isa( 'PPI::Token::Word' )
            or return;
        'do' eq $prev->content()
            or return;

        $cast = $prev->sprevious_sibling()

    }

    $cast
        or return;
    $cast->isa( 'PPI::Token::Cast' )
        or return;
    return q<\\> eq $cast->content()
}

#-----------------------------------------------------------------------------

Readonly::Hash my %CAST_ALLOWED_FOR_BARE_BRACKETED_VARIABLE => hashify(
    qw{ @ $ % } );

sub _get_symbol_uses {
    my ( $document, $scope_of_record, $declared, $is_declaration ) = @_;

    foreach my $symbol ( @{ $document->find( 'PPI::Token::Symbol' ) || [] } )
    {
        $is_declaration->{ refaddr( $symbol ) } and next;

        my $scope = $scope_of_record ||
            Perl::Critic::Utils::Scope->new( $symbol );

        _record_symbol_use( _get_symbol_name( $symbol ), $scope, $declared );

    }

    # For some reason, PPI parses '$#foo' as a PPI::Token::ArrayIndex.
    # $#$foo is parsed as a Cast followed by a Symbol, so as long as
    # nobody decides the '$#' cast causes _get_symbol_name (or, ideally,
    # $elem->symbol()) to return something other than '$foo', we're cool.
    foreach my $elem ( @{ $document->find( 'PPI::Token::ArrayIndex' ) || [] }
    ) {

        my $name = $elem->content();
        $name =~ s/ \A \$ [#] /@/smx or next;

        my $scope = $scope_of_record ||
            Perl::Critic::Utils::Scope->new( $elem );

        _record_symbol_use( $name, $scope, $declared );
    }

    # Occasionally you see something like ${foo} outside quotes. This is
    # legitimate, though PPI parses it as a cast followed by a block. On
    # the assumption that there are fewer blocks than words in most
    # Perl, we start at the top and work down. Perl also handles
    # punctuation variables specified this way, but since PPI goes
    # berserk when it sees this, we won't bother.
    foreach my $elem ( @{ $document->find( 'PPI::Structure::Block' ) ||
        [] } ) {

        my $previous = $elem->sprevious_sibling()
            or next;
        $previous->isa( 'PPI::Token::Cast' )
            or next;
        my $sigil = $previous->content();
        $CAST_ALLOWED_FOR_BARE_BRACKETED_VARIABLE{ $sigil }
            or next;

        my @kids = $elem->schildren();
        1 == @kids
            or next;
        $kids[0]->isa( 'PPI::Statement' )
            or next;

        my @grand_kids = $kids[0]->schildren();
        1 == @grand_kids
            or next;
        $grand_kids[0]->isa( 'PPI::Token::Word' )
            or next;

        my $scope = $scope_of_record ||
            Perl::Critic::Utils::Scope->new( $elem );

        _record_symbol_use( $sigil . $grand_kids[0]->content(),
            $scope, $declared );
    }

    return;
}

#-----------------------------------------------------------------------------

sub _record_symbol_use {
    my ( $symbol_name, $scope, $declared ) = @_;
    my $declaration = $declared->{ $symbol_name }
        or return;

    foreach my $decl_scope ( @{ $declaration } ) {
        $decl_scope->{scope}->is_visible_after_statement( $scope )
            or next;
        $decl_scope->{used}++;
        last;
    }

    return;

}

#-----------------------------------------------------------------------------

sub _get_double_quotish_string_uses {
    my ( $document, $scope_of_record, $declared ) = @_;

    foreach my $class ( qw{
        PPI::Token::Quote::Double
        PPI::Token::Quote::Interpolate
        PPI::Token::QuoteLike::Backtick
        PPI::Token::QuoteLike::Command
        PPI::Token::QuoteLike::Readline
        } ) {
        foreach my $double_quotish ( @{ $document->find( $class ) || []
            } ) {
            my $string = $double_quotish->content();

            # qx'...' does not interpolate
            $double_quotish->isa( 'PPI::Token::QuoteLike::Command' )
                and $string =~ m/ \A qx \s* ' /smx
                and next;

            my $scope = $scope_of_record ||
                Perl::Critic::Utils::Scope->new( $double_quotish );
            _extract_interpolations( $string, $scope, $declared );
        }
    }

    return;
}

#-----------------------------------------------------------------------------

sub _extract_interpolations {
    my ( $string, $scope, $declared ) = @_;
    while ( $string =~ m/ $FIND_INTERPOLATION /smxgo ) {
        my ( $sigil, $name, $brace ) = ( $1, $2, $3 );
        my $symbol =
            _compute_symbol_from_interpolation_pieces_parts(
            $sigil, $name, $brace );
        _record_symbol_use( $symbol, $scope, $declared );
    }
    return;
}

#-----------------------------------------------------------------------------

sub _get_here_document_uses {
    my ( $document, $declared ) = @_;

    foreach my $here_document ( @{ $document->find(
        'PPI::Token::HereDoc' ) || []
        } ) {

        $here_document->content() =~ m/ \A << \s* ' /smx
            and next;

        my $scope = Perl::Critic::Utils::Scope->new( $here_document );

        foreach my $string ( $here_document->heredoc() ) {

            _extract_interpolations( $string, $scope, $declared );

        }
    }

    return;
}

#-----------------------------------------------------------------------------

Readonly::Hash my %SIGIL_TO_BE_TAKEN_AS_IS => hashify( qw{ @$ $$ @ } );
Readonly::Hash my %SIGIL_COMPUTED_FROM_BRACE => (
    q<{>    => q<%>,
    q<[>    => q<@>,
);

sub _compute_symbol_from_interpolation_pieces_parts {
    my ( $cast_and_sigil, $name, $brace ) = @_;

    $name =~ s/ \A [{] //smx;
    $name =~ s/ [}] \z //smx;

    my $sigil = substr $cast_and_sigil, $LAST_CHARACTER;

    $SIGIL_TO_BE_TAKEN_AS_IS{$cast_and_sigil}
        and return "$sigil$name";

    defined(
        my $computed_sigil =
            $SIGIL_COMPUTED_FROM_BRACE{ $brace || $EMPTY }
    ) or return "$sigil$name";

    return "$computed_sigil$name";

}

#-----------------------------------------------------------------------------

sub _get_regexp_symbol_uses {
    my ( $document, $declared, $is_declaration ) = @_;

    foreach my $class ( qw{
        PPI::Token::Regexp::Match
        PPI::Token::Regexp::Substitute
        PPI::Token::QuoteLike::Regexp
        } ) {

        foreach my $regex ( @{ $document->find( $class ) || [] } ) {

            my $ppix = $document->ppix_regexp_from_element( $regex ) or next;
            $ppix->failures() and next;

            my $scope_of_record = Perl::Critic::Utils::Scope->new( $regex );

            foreach my $code ( @{
                $ppix->find( 'PPIx::Regexp::Token::Code' ) || [] } ) {

                my $subdoc = $code->ppi() or next;

                _get_symbol_uses( $subdoc, $scope_of_record,
                    $declared, $is_declaration );

                # Yes, someone did s/.../"..."/e.
                _get_double_quotish_string_uses( $subdoc,
                    $scope_of_record, $declared );

            }

        }

    }

    return;
}

#-----------------------------------------------------------------------------

#   This subroutine is a workaround for PPI bug #65199. The problem is
#   that PPI (at least as of 1.213) does not take into account the fact
#   that (e.g.) $$foo{bar} is equivalent to $foo->{bar}, and thinks the
#   former makes use of %foo.

Readonly::Hash my %CAST_WHICH_TRUMPS_BRACES => hashify( qw{ $ @ } );
sub _get_symbol_name {
    my ( $elem ) = @_;  # Assumed to be a PPI::Token::Symbol
    my $name = $elem->symbol();
    my $cast = $elem->sprevious_sibling()
        or return $name;
    $cast->isa( 'PPI::Token::Cast' )
        or return $name;
    $CAST_WHICH_TRUMPS_BRACES{ $cast->content() }
        or return $name;
    my $type = substr $elem->canonical(), 0, 1;
    q<$> eq $type
        and $name =~ s/ \A [%\@] /\$/smx;
    return $name;
}


#-----------------------------------------------------------------------------

sub _get_violations {
    my ( $self, $declared ) = @_;

    my @in_violation;

    foreach my $name ( values %{ $declared } ) {
        foreach my $declaration ( @{ $name } ) {
            $declaration->{is_global} and next;
            $declaration->{used} and next;
            $declaration->{is_allowed_computation} and next;
            $declaration->{taking_reference}
                and not $self->{_prohibit_reference_only_variables}
                and next;
            $declaration->{is_unpacking}
                and not $self->{_prohibit_unused_subroutine_arguments}
                and next;
            push @in_violation, $declaration->{element};
        }
    }

    return ( map { $self->violation(
            sprintf( '%s is declared but not used', _get_symbol_name( $_ ) ),
            $EXPL,
            $_
        ) } sort { $a->line_number() <=> $b->line_number() ||
            $a->column_number() <=> $b->column_number() }
        @in_violation );
}

#-----------------------------------------------------------------------------

1;

__END__

#-----------------------------------------------------------------------------

=pod

=head1 NAME

Perl::Critic::Policy::Variables::ProhibitUnusedVariables - Don't ask for storage you don't need.


=head1 AFFILIATION

This Policy is part of the core L<Perl::Critic|Perl::Critic>
distribution.


=head1 DESCRIPTION

Unused variables clutter code and require the reader to do mental
bookkeeping to figure out if the variable is actually used or not.

Right now, this only looks for lexical variables which are unused other
than in the statement that declares them.

    my $x;          # not ok, assuming no other appearances.
    my @y = ();     # not ok, assuming no other appearances.
    our $z;         # ok, global.
    local $w;       # ok, global.

This policy attempts not to report unused variables that are declared as
part of unpacking subroutine arguments. That is, in code like

    my ( $self, $arg ) = @_;
    my $arg = shift;
    my $arg = shift @_;
    my $arg = $_[1];

it will not report a violation if C<$arg> is unused. The rationale here
is that for consistency and/or future expansion subroutines may have
unused arguments. Only fairly simple unpacking methods such as those
above are understood by this logic; something like

    my $class = ref $_[0] || $_[0];

will be reported anyway if C<$class> is unused.

This policy also intentionally does not report variables as unused if
the code takes a reference to the variable, even if it is otherwise
unused. For example things like

    \( my $foo = 'bar' )
    \do{ my $foo => 'bar' }

will not be reported as a violation even if C<$foo> is otherwise unused.
The reason is that this is an idiom for making a reference to a mutable
string when all you have is an immutable string. This policy does not
check to see if anything is done with the reference.

This policy also does not detect unused variables declared inside
various odd corners such as

    s///e
    qr{(?{...})}
    qr{(??{...})}
    "@{[ ... ]}"
    ( $foo, my $bar ) = ( 1, 2 )

Most of these are because the PPI parse of the original document does
not include the declarations. The list assignment is missed because PPI
does not parse it as containing a
L<PPI::Statement::Variable|PPI::Statement::Variable>. However, variables
B<used> inside such construction B<will> be detected.


=head1 CONFIGURATION

By default, this policy allows unused subroutine arguments. If you wish
to declare a violation on unused subroutine arguments, you can add a
block like this to your F<.perlcriticrc> file:

    [Variables::ProhibitUnusedVariables]
    prohibit_unused_subroutine_arguments = 1

By default, this policy allows otherwise-unused variables if the code
takes a reference to the variable when it is created. If you wish to
declare a violation in this case, you can add a block like this to your
F<.perlcriticrc> file:

    [Variables::ProhibitUnusedVariables]
    prohibit_reference_only_variables = 1

You may wish to allow variables to be unused when computed in certain
ways. For example, you might want to allow place-holder variables in a
list computed by C<stat()> or C<unpack()>. Or you may be doing
end-of-scope detection with something like
C<< my $foo = Scope::Guard->new( \&end_of_scope ) >>. To ignore all
these, you can add a block like this to your F<.perlcriticrc> file:

    [Variables::ProhibitUnusedVariables]
    allow_if_computed_by = stat unpack Scope::Guard

This property takes as its value a whitespace-delimited list of class or
subroutine names. Nothing complex is done to implement this -- the
policy simply looks at the first word after the equals sign, if any.


=head1 AUTHOR

Elliot Shank C<< <perl@galumph.com> >>


=head1 COPYRIGHT

Copyright (c) 2008-2011 Elliot Shank.

This program is free software; you can redistribute it and/or modify
it under the same terms as Perl itself.  The full text of this license
can be found in the LICENSE file included with this module.

=cut

# Local Variables:
#   mode: cperl
#   cperl-indent-level: 4
#   fill-column: 78
#   indent-tabs-mode: nil
#   c-indentation-style: bsd
# End:
# ex: set ts=8 sts=4 sw=4 tw=78 ft=perl expandtab shiftround :
