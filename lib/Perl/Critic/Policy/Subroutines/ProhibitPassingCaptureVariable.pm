##############################################################################
#      $URL$
#     $Date$
#   $Author$
# $Revision$
##############################################################################

package Perl::Critic::Policy::Subroutines::ProhibitPassingCaptureVariable;

use 5.006001;
use strict;
use warnings;

use Readonly;

use version;

use base 'Perl::Critic::Policy';

use Perl::Critic::Utils qw{ :severities :classification :ppi :booleans
                            :language };
use PPI;
use PPI::Document;

our $VERSION = '1.110';

#-----------------------------------------------------------------------------

Readonly::Scalar my $DESC => q{Capture variable "%s" passed to subroutine "%s"};
Readonly::Scalar my $EXPL =>
q{Any regular expression in the subroutine may modify the caller's copy};

Readonly::Scalar my $MINIMUM_NAMED_CAPTURE_VERSION => version->new(5.010);
Readonly::Scalar my $PERCENT_PLUS => q{%+};
Readonly::Scalar my $PERCENT_MINUS => q{%-};
Readonly::Hash my %NAMED_CAPTURE_BUFFER => (
    $PERCENT_PLUS => 1,
    $PERCENT_MINUS => 1,
);

# Operators that do not cause a new value to be computed from their operands.
Readonly::Hash my %UNCLEAN_OPERATOR => (
    q{||}   => 1,
    q{//}   => 1,
    q{&&}   => 1,
    q{and}  => 1,
    q{or}   => 1,
    q{xor}  => 1,
    q{,}    => 1,
    q{=>}   => 1,
);

# Containers that cause a new value to be computed from their operands.
Readonly::Hash my %CLEAN_CONTAINER => (
    q{PPI::Structure::Subscript} => 1,
);

#-----------------------------------------------------------------------------

sub supported_parameters {
    return (
        {
            name        => 'allow_subroutines',
            description => 'Subroutines which sanitize their arguments',
            behavior    => 'string list',
        },
    )
}
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

    return ( $self->_is_violation( $elem, $document, $perl_version ) );
}

#-----------------------------------------------------------------------------

# This method returns a violation object for any capture variables found
# to be in violation of the policy. It is really just a dispatcher,
# since the logic of finding a violation depends on the object being
# analyzed. The $perl_version has to be carried along because we may be
# analyzing a bare PPI::Document rather than a Perl::Critic::Document.

Readonly::Hash my %CLASS_HANDLER => (
    'PPI::Token::Regexp::Substitute' => \&_handle_substitute,
    'PPI::Token::Word' => \&_handle_call,
);

sub _is_violation {
    my ( $self, $elem, $document, $perl_version ) = @_;
    my $elem_class = ref $elem or return;
    $CLASS_HANDLER{$elem_class} or return;
    return $CLASS_HANDLER{$elem_class}->($self, $elem, $document,
        $perl_version );
}

#-----------------------------------------------------------------------------

# This subroutine analyzes PPI::Token::Regexp::Substitute objects, and
# returns a list of violation objects for aby offending variables found.

sub _handle_substitute {
    my ( $self, $elem, $document, $perl_version ) = @_;

    my $regexp = $document->ppix_regexp_from_element( $elem )
        or return;

    my $replace = $regexp->replacement()
        or return;

    # The following cribbed shamelessly from Perl::Critic::_critique
    # CAVEAT: it relies on prepare_to_scan_document() doing nothing.

    my @violations;
    foreach my $code_element ( @{ $replace->find( 'PPIx::Regexp::Token::Code' )
        || [] } ) {

        my $code_doc = $code_element->ppi();
        foreach my $type ( $self->applies_to() ) {

            foreach my $element ( @{ $code_doc->find( $type ) || [] } ) {

                push @violations, $self->_is_violation(
                    $element, $code_doc, $perl_version );
            }

        }

    }

    return @violations;

}

#-----------------------------------------------------------------------------

# This subroutine analyzes PPI::Token::Word objects.

# Barewords are of interest only if they represent function or method calls,
# with arguments. For anything else, we return nothing.
#
# Given a subroutine or method call, we return violation objects for any
# variables found in violation of the policy. The $perl_version must be
# explicit because we may be analyzing a PPI::Document rather than the
# original Perl::Critic::Document.

sub _handle_call {
    my ( $self, $elem, $document, $perl_version ) = @_;

    # We are only interested in method and function calls which are not Perl
    # built-ins.
    ( is_method_call( $elem ) || is_function_call( $elem ) )
        or return;
    is_perl_builtin( $elem ) and return;

    my $subroutine = $elem->content();
    $self->{_allow_subroutines}{ $subroutine }
        and return;

    return ( map { $self->violation(
        sprintf( $DESC, $_->content(), $subroutine ), $EXPL, $_ ) }
        _find_uncleaned_capture_variables_in_args( $perl_version, $elem )
    );

}

#-----------------------------------------------------------------------------

# @captures = _find_uncleaned_capture_variables_in_args(
#     $perl_version, $elem );
#
# This subroutine assumes $elem is a subroutine call, and returns all
# un-sanitized capture variables for the given $perl_version which are found
# in the argument list.

sub _find_uncleaned_capture_variables_in_args {
    my ( $perl_version, $elem ) = @_;

    my @rslt;
    foreach my $arg ( parse_arg_list( $elem ) ) {

        foreach my $capture (
            grep { _is_capture_variable( $perl_version, $_ ) }
            map { $_->isa( 'PPI::Node' ) ?
            @{ $_->find( 'PPI::Token::Magic' ) || [] } :
            $_ } @{ $arg } ) {

            _is_value_cleaned( $capture, $arg->[0], $TRUE )
                or _is_value_cleaned( $capture, $arg->[-1] )
                or push @rslt, $capture;

        }
    }

    return @rslt;
}

#-----------------------------------------------------------------------------

# $elem = _is_capture_variable( $perl_version, $elem );
#
# This subroutine returns the $elem argument if it is a capture variable under
# the given $perl_version. Otherwise it returns nothing. If $perl_version is
# undef, we assume we are dealing with an 'old' Perl, that does not understand
# named captures.

sub _is_capture_variable {
    my ( $perl_version, $elem ) = @_;

    $elem or return;

    $elem->isa( 'PPI::Token::Magic' )
        or return;

    my $symbol = $elem->symbol();

    if ( $symbol =~ m/ \A \$ ( \d+ ) \z /smx ) {
        $1 and return $elem;
        return;
    }

    $perl_version
        or return;

    $MINIMUM_NAMED_CAPTURE_VERSION <= $perl_version
        and $NAMED_CAPTURE_BUFFER{$symbol}
        and return $elem;

    return;

}

#-----------------------------------------------------------------------------

# $boolean = _is_value_cleaned( $elem, $stop, $scan_left );
#
# This subroutine scans in the indicated direction (left if $scan_left
# is true, otherwise right) until it either finds an operator that
# sanitizes the value of the given $elem, or until it hits the $stop
# element. In the former case it returns true; in the latter it returns
# false.

sub _is_value_cleaned {

    my ( $elem, $stop, $scan_left ) = @_;
    my $next_sibling = $scan_left ? 'previous_sibling' : 'next_sibling';

    my $limiting_precedence = 0;

    while ( $elem ) {

        $elem->significant()
            or next;

        if ( $elem->isa( 'PPI::Token::Operator' ) ) {

            my $content = $elem->content();
            my $precedence = precedence_of( $content );
            $precedence < $limiting_precedence
                and next;

            $UNCLEAN_OPERATOR{ $elem->content() }
                or return $TRUE;
            $limiting_precedence = $precedence;

        } elsif ( $scan_left && $elem->isa( 'PPI::Token::Word' ) &&
            ( is_method_call( $elem ) || is_function_call( $elem ) ) ) {

            # The following is a little white lie. We're actually pretty
            # sure at this point that the value is _not_ sanitized, but
            # we also know that we have found a subroutine call that we
            # will encounter later. So we abort the scan now to prevent
            # double-reporting the problem. And besides, when we look at
            # the subroutine in detail, we might find that it sanitizes
            # the value.

            return $TRUE;

        }

    } continue {

        $elem == $stop and last;

        if ( my $sib = $elem->$next_sibling() ) {
            $elem = $sib;
        } else {
            $elem = $elem->parent()
                or return;
            $CLEAN_CONTAINER{ ref $elem }
                and return $TRUE;
            $limiting_precedence = 0;
        }
    }

    return;
}

#-----------------------------------------------------------------------------

1;

__END__

#-----------------------------------------------------------------------------

=pod

=for stopwords builtins

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

This Policy has a single configuration option: C<allowed_subroutines>.

The C<allowed_subroutines> option allows you to configure the names of
subroutines which sanitize their arguments before use. For example,
the argument of

 sub decrement {
     my ( $arg ) = @_;
     return --$arg;
 }

is sanitized by being copied out of @_. You can tell this policy to
ignore C<decrement()> by adding something like the following to your
F<.perlcriticrc> file:

 [Subroutines::ProhibitPassingCaptureVariable]
 allow_subroutines = decrement

Multiple names are specified blank-delimited; to exempt both
C<decrement()> and C<increment()>, specify

 [Subroutines::ProhibitPassingCaptureVariable]
 allow_subroutines = decrement increment

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

Cases like C<< foo( sprintf '%s', $1 ) >> are not currently handled
correctly because of the difficulty of correctly picking apart the
argument list. When the C<parse_arg_list()> utility sees C<foo()> as
receiving a single argument, this should 'just work.'.
C<< foo( sprintf( '%s', $1 ) ) >> should be handled correctly.

=head1 AUTHOR

Thomas R. Wyant, III F<wyant at cpan dot org>.

=head1 COPYRIGHT

Copyright 2009-2010 Thomas R. Wyant, III.

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
