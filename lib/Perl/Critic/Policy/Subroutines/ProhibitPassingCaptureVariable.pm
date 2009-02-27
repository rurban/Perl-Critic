##############################################################################
#      $URL: http://perlcritic.tigris.org/svn/perlcritic/trunk/distributions/Perl-Critic/lib/Perl/Critic/Policy/InputOutput/ProhibitTwoArgOpen.pm $
#     $Date: 2009-01-01 19:06:43 -0600 (Thu, 01 Jan 2009) $
#   $Author: clonezone $
# $Revision: 2949 $
##############################################################################

package Perl::Critic::Policy::Subroutines::ProhibitPassingCaptureVariable;

use 5.006001;
use strict;
use warnings;

use Readonly;

use version;

use base 'Perl::Critic::Policy';

use Perl::Critic::Utils qw{ :severities :classification :ppi :booleans };
use Perl::Critic::Utils::PPIRegexp qw(get_modifiers get_substitute_string);
use PPI;
use PPI::Document;

our $VERSION = '1.096';

#-----------------------------------------------------------------------------

Readonly::Scalar my $DESC => q{Capture variable "%s" passed to subroutine "%s"};
Readonly::Scalar my $EXPL =>
q{Any regular expression in the subroutine will modify the caller's copy};

Readonly::Scalar my $MINIMUM_NAMED_CAPTURE_VERSION => version->new(5.010);
Readonly::Scalar my $PERCENT_PLUS => q{%+};
Readonly::Scalar my $PERCENT_MINUS => q{%-};
Readonly::Hash my %NAMED_CAPTURE_BUFFER => (
    $PERCENT_PLUS => 1,
    $PERCENT_MINUS => 1,
);

#-----------------------------------------------------------------------------

sub supported_parameters { return ()                         }
sub default_severity     { return $SEVERITY_HIGH             }
sub default_themes       { return qw(core bugs)              }
sub applies_to           { return (qw(
                                PPI::Token::Word
                                PPI::Token::Regexp::Substitute)
                            )
                         }

#-----------------------------------------------------------------------------

sub violates {
    my ( $self, $elem, $document ) = @_;

    $elem or return;

    my $perl_version = $document->highest_explicit_perl_version();

    my @violations;
    foreach my $info ( $self->_is_violation( $elem, $perl_version ) ) {
        my $msg = sprintf $DESC, $info->{var}, $info->{sub};
        push @violations, $self->violation( $msg, $EXPL, $elem );
    }
    return @violations;
}

#-----------------------------------------------------------------------------

# This method returns a hash describing any capture variables found to be in
# violation of the policy. It is really just a dispatcher, since the logic of
# finding a violation depends on the object being analyzed.

Readonly::Hash my %CLASS_HANDLER => (
    'PPI::Token::Regexp::Substitute' => \&_handle_substitute,
    'PPI::Token::Word' => \&_handle_call,
);

sub _is_violation {
    my ( $self, $elem, $perl_version ) = @_;
    my $elem_class = ref $elem or return;
    $CLASS_HANDLER{$elem_class} or return;
    return $CLASS_HANDLER{$elem_class}->($self, $elem, $perl_version);
}

#-----------------------------------------------------------------------------

# This subroutine analyzes PPI::Token::Regexp::Substitute objects, and returns
# a list of hashes containing the names of the offending variables and
# subroutines, if any.
#
# Substitutions are of interest only if they have the 'e' modifier. If they
# do, the substitution is a Perl expression, and must be parsed as such. This
# is done by constructing a PPI document from it, and using that document to
# recurse into the _is_violation() method.

sub _handle_substitute {
    my ( $self, $elem, $perl_version ) = @_;

    my %modifiers = get_modifiers( $elem );
    $modifiers{e} or return;

    my $substitution = get_substitute_string( $elem );

    my $document = PPI::Document->new( \$substitution );

    # The following cribbed shamelessly from Perl::Critic::_critique
    # CAVEAT: it relies on prepare_to_scan_document() doing nothing.

    my @violations;
    foreach my $type ( $self->applies_to() ) {
        foreach my $element ( @{ $document->find( $type ) || []} ) {
            push @violations, $self->_is_violation( $element, $perl_version );
        }
    }

    return @violations;

}

#-----------------------------------------------------------------------------

# This subroutine analyzes PPI::Token::Word objects.

# Barewords are of interest only if they represent function or method calls,
# with arguments. We find all PPI::Token::Magic objects in the argument list
# that represent substitution variables, and return a list of hashes,
# containing the names of variables not rendered harmless by adjacent
# operators, and the names of the subroutines they were passed to.

Readonly::Hash my %ARGUMENT_LIST_END => (
    'PPI::Token::Structure' => {
        q{;} => 1,
    },
    'PPI::Token::Operator' => {
        q{and} => 1,
        q{or} => 1,
        q{dor} => 1,
    },
);

sub _handle_call {
    my ( $self, $elem, $perl_version ) = @_;

    (is_method_call( $elem ) || is_function_call( $elem ))
        or return;
    is_perl_builtin( $elem ) and return;

    my $next = $elem->snext_sibling()
        or return;

    $next->isa( 'PPI::Structure::List' ) or do {
        my $doc = PPI::Document->new();
        my $working_element = $next;

        while ( $working_element ) {
            my $class = ref $working_element;
            my $content = $working_element->content();
            $ARGUMENT_LIST_END{$class}
                and $ARGUMENT_LIST_END{$class}{$content}
                and last;
        } continue {
            $doc->add_element( $working_element->clone() );
            $working_element = $working_element->next_sibling();
        }

        $next = $doc;
    };

    my @violations;

    foreach my $capture (
        $self->_find_capture_variables( $next, $perl_version ) ) {

        $self->_check_adjacent_operators( $capture, $next )
            and push @violations, {
                var => $capture->symbol(),
                sub => $elem->content(),
            };

    }

    return @violations;

}

#-----------------------------------------------------------------------------

# This method finds capture variables in the given element, which must be a
# PPI::Node. It uses PPI::Node->find() to do the heavy lifting, with the
# \&wanted routine being determined by the given Perl version.

sub _find_capture_variables {
    my ( $self, $elem, $perl_version ) = @_;

    my $finder = (
        $perl_version &&
        $MINIMUM_NAMED_CAPTURE_VERSION <= $perl_version
    ) ? \&_find_capture_var_5010 : \&_find_capture_var_5008;

    return @{ $elem->find( $finder ) || [] };
}

#-----------------------------------------------------------------------------

# This subroutine is the PPI::Node->find(\&wanted) routine to be used with
# versions of Perl below 5.010.

sub _find_capture_var_5008 {
    my ( undef, $elem ) = @_;
    $elem->isa( 'PPI::Token::Magic' ) or return $FALSE;
    ($elem->symbol() =~ m/ \A \$ ( \d+ ) \z /smx && $1) and return $TRUE;
    return $FALSE;
}

#-----------------------------------------------------------------------------

# This subroutine is the PPI::Node->find(\&wanted) routine to be used with
# Perl 5.010 and above.

sub _find_capture_var_5010 {
    my ( undef, $elem ) = @_;
    $elem->isa( 'PPI::Token::Magic' ) or return $FALSE;
    my $symbol = $elem->symbol();
    ($symbol =~ m/ \A \$ ( \d+ ) \z /smx && $1) and return $TRUE;
    $NAMED_CAPTURE_BUFFER{$symbol} and return $TRUE;
    return $FALSE;
}

#-----------------------------------------------------------------------------

# This method checks operators adjacent to the given element (assumed to be a
# PPI::Token::Magic) to see if they cause a new value to be computed. If they
# do, nothing is returned. If they do not the name of the PPI::Token::Magic
# symbol is returned. We do not return the object itself, because it may have
# come from a document synthesized in the course of analysis, and become
# undefined before we can use it.
#
# We assume any operator other than those in the list below causes value to be
# computed. If we do not get a new value from one of the adjacent operators we
# do the same analysis on the parent object, repeating until we come to the
# specified ultimate container. If at that point we still have not found an
# operator that causes a new value to be generated, we return the offending
# symbol name.

Readonly::Hash my %UNCLEAN_OPERATOR => (
    q{||}   => 1,
    q{//}   => 1,
    q{&&}   => 1,
    q{and}  => 1,
    q{or}   => 1,
    q{dor}  => 1,
    q{,}    => 1,   # Here for convenience.
    q{=>}   => 1,   # Here for convenience.
);
Readonly::Hash my %CLEAN_CONTAINER => (
    q{PPI::Structure::Subscript} => 1,
);

sub _check_adjacent_operators {
    my ( $self, $elem, $ultimate_container ) = @_;

    my $check = $elem;
    while ( $check != $ultimate_container ) {

        $CLEAN_CONTAINER{ ref $check } and return;

        my $prev_oper = _find_operator(
            $check, sub { $_[0]->sprevious_sibling() } );
        my $next_oper = _find_operator(
            $check, sub { $_[0]->snext_sibling() } );

        foreach my $oper ( $prev_oper, $next_oper ) {
            $oper or next;
            $UNCLEAN_OPERATOR{$oper} or return;
        }

        $check = $check->parent()
            or last;

    }

    return $TRUE;

}

#-----------------------------------------------------------------------------

# This subroutine finds the operator adacent to the given element in the
# direction indicated by the advance argument (which is a reference to code
# that finds the next token). The content of the PPI::Token::Operator object
# is returned. If no operator is found, nothing is returned.

sub _find_operator {
    my ( $elem, $advance ) = @_;
    my $oper = $elem;
    while ($oper = $advance->($oper)) {
        $oper->isa( 'PPI::Token::Operator' ) and return $oper->content();
    }
    return;
}

1;

__END__

#-----------------------------------------------------------------------------

=pod

=head1 NAME

Perl::Critic::Policy::Subroutines::ProhibitPassingCaptureVariable - Do not pass capture variables as arguments.

=head1 AFFILIATION

This Policy is part of the core L<Perl::Critic|Perl::Critic>
distribution.

=head1 DESCRIPTION

Passing capture variables such as $1 as arguments to a subroutine is unwise,
since any regular expression operation in the subroutine will modify them,
with unexpected consequences for the caller. Using a capture variable in an
expression that is passed to a subroutine is OK if the expression actually
causes a new value to be computed.

  foo($1, $2);              # not OK
  foo("$1", +$2);           # OK
  foo($1 || 1);             # not OK
  foo(($1 || 1) + 1);       # OK

If the document being analyzed contains an explicit C<< use 5.010; >> usage of
the named capture hashes will also be checked.

Perl builtins are assumed to be clean, and are exempt from this policy.

This Policy is a response to RT 38289. The following script adapted from RT
38289 illustrates the problem:

  #!/usr/local/bin/perl
  
  use strict;
  use warnings;
  
  my $options = 'hello';
  sub f {
      print "hello\n" if $options =~ /hello/;
      print "args are @_\n";
      return;
  }
  $_ = 'foo';
  if (/(\w+)/) {
      f($1);
  }

=head1 CONFIGURATION

This Policy is not configurable except for the standard options.

=head1 CAVEATS

Calls to code references (e.g. C<< $foo->( $1 ) >>) are not checked. Neither
are indirect method calls (e.g. C<< $foo->$bar( $1 ) >>).

The builtins introduced in Perl 5.010 may not be properly exempted from
analysis. Specifically, things like C<say> may not be recognized as builtins
when the analysis is run under Perl 5.008 or below, even if the code
contains an explicit C<< use 5.010; >>. Similarly, things like C<say> may be
considered builtins when the analysis is run under Perl 5.010, even if the
code does not contain an explicit C<< use 5.010; >>.

Because the operators that do not compute new values (C<||> and friends) bind
rather loosely, expression analysis is limited to adjacent operators. This may
not produce correct results in all cases, though it is sufficient for the
analysis of Perl::Critic itself.

Substitutions whose right side contains a here document do not seem to be
parsed correctly by PPI, so analysis of documents containing such code may
produce anomalous results.

=head1 AUTHOR

Thomas R. Wyant, III F<wyant at cpan dot org>.

=head1 COPYRIGHT

Copyright 2009 Thomas R. Wyant, III.

This program is free software; you can redistribute it and/or modify
it under the same terms as Perl itself.

=cut

# Local Variables:
#   mode: cperl
#   cperl-indent-level: 4
#   fill-column: 78
#   indent-tabs-mode: nil
#   c-indentation-style: bsd
# End:
# ex: set ts=8 sts=4 sw=4 tw=78 ft=perl expandtab shiftround :
