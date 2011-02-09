##############################################################################
#      $URL$
#     $Date$
#   $Author$
# $Revision$
##############################################################################

package Perl::Critic::Utils::Scope;

use 5.006001;
use strict;
use warnings;

use Readonly;

use Scalar::Util qw< blessed >;

our $VERSION = '1.112_001';

Readonly::Scalar my $LAST_ELEMENT_INDEX => -1;
Readonly::Array my @SCOPE_CLASS =>
    qw{ PPI::Document PPI::Structure::Block PPI::Statement::Compound };

#-----------------------------------------------------------------------------

sub new {
    my ( $class, $elem ) = @_;

    blessed( $elem ) or return;
    $elem->isa( 'PPI::Element' ) or return;

    ref $class and $class = ref $class;

    my @scope;
    my $parent = $elem->parent();
    while ( $parent ) {
        foreach my $class ( @SCOPE_CLASS ) {
            $parent->isa( $class ) or next;
            push @scope, $parent;
            last;
        }
        $parent = $parent->parent();
    }

    my $self = {
        _column_number => $elem->column_number(),
        _element => $elem,
        _line_number => $elem->line_number(),
        _scope   => [ reverse @scope ],
    };

    if ( my $statement = $elem->statement() ) {
        my $last_element = $statement->child( $LAST_ELEMENT_INDEX );
        $self->{_after_column} = $last_element->column_number();
        $self->{_after_line} = $last_element->line_number();
    }

    return bless $self, $class;
}

#-----------------------------------------------------------------------------

sub element {
    my ( $self ) = @_;
    return $self->{_element};
}

#-----------------------------------------------------------------------------

sub is_visible_after_statement {
    my ( $self, $elem ) = @_;

    defined $self->{_after_column}
        and defined $self->{_after_line}
        or return;

    blessed( $elem ) or return;
    $elem->isa( __PACKAGE__ ) or return;

    $elem->{_line_number} < $self->{_after_line}
        and return;
    $elem->{_line_number} == $self->{_after_line}
        and $elem->{_column_number} <= $self->{_after_column}
        and return;

    my $inx = @{ $self->{_scope} } - 1;
    @{ $elem->{_scope} } <= $inx
        and return;

    return $self->{_scope}[$inx] == $elem->{_scope}[$inx];

}

#-----------------------------------------------------------------------------

# TODO get rid of this. It is only used to trouble-shoot scope computations.
sub __dump_scope {
    my ( $self ) = @_;
    my $output = $self->{_element}->content() . "\n";
    foreach my $scope ( @{ $self->{_scope} } ) {
        $output .= sprintf "    %s %d %d\n", ref $scope,
            $scope->line_number(),
            $scope->column_number();
    }
    return $output;
}

#-----------------------------------------------------------------------------

1;

__END__

=pod

=for stopwords invocant's

=head1 NAME

Perl::Critic::Utils::Scope - Utility object representing a Perl scope.


=head1 DESCRIPTION

Provides computations relating to the scope of a <PPI::Element|PPI::Element>.

This class considers a scope to be defined by a
L<PPI::Document|PPI::Document>, a
L<PPI::Structure::Block|PPI::Structure::Block>, or a
L<PPI::Statement::Compound|PPI::Statement::Compound>.


=head1 INTERFACE SUPPORT

This module is considered B<private> to C<Perl::Critic>. It (and its
interface) may be changed without notice.


=head1 METHODS

=over

=item C<new( $element )>

Instantiates a C<Perl::Critic::Utils::Scope> object. The parameter must
be a L<PPI::Element|PPI::Element>.


=item C<element()>

Returns the L<PPI::Element|PPI::Element> that was originally passed to
C<new()>.


=item C<is_visible_after_statement( $element )>

Answers the question of whether the given element is visible after the
statement in which the invocant's L<PPI::Element|PPI::Element> occurs.
For this to be true, the element must be after the last element in the
invocant's statement, and the element must be in the invocant's
most-local scope.

The parameter must be a C<Perl::Critic::Utils::Scope>. If not, the
method returns a false value.


=back


=head1 AUTHOR

Thomas R. Wyant, III F<wyant at cpan dot org>


=head1 COPYRIGHT

Copyright (c) 2011 Thomas R. Wyant, III

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
