##############################################################################
#      $URL$
#     $Date$
#   $Author$
# $Revision$
##############################################################################

package Perl::Critic::Policy::Documentation::RequirePodSections;

use strict;
use warnings;
use Readonly;

use Perl::Critic::Utils qw{ :booleans :characters :severities :classification };
use base 'Perl::Critic::Policy';

our $VERSION = 1.073;

#-----------------------------------------------------------------------------

Readonly::Scalar my $EXPL => [133, 138];

Readonly::Scalar my $BOOK                => 'book';
Readonly::Scalar my $BOOK_FIRST_EDITION  => 'book_first_edition';
Readonly::Scalar my $MODULE_STARTER_PBP  => 'module_starter_pbp';
Readonly::Scalar my $M_S_PBP_0_0_3       => 'module_starter_pbp_0_0_3';

Readonly::Scalar my $DEFAULT_SOURCE      => $BOOK_FIRST_EDITION;

my %SOURCE_TRANSLATION  = (
    $BOOK               => $BOOK_FIRST_EDITION,
    $BOOK_FIRST_EDITION => $BOOK_FIRST_EDITION,
    $MODULE_STARTER_PBP => $M_S_PBP_0_0_3,
    $M_S_PBP_0_0_3      => $M_S_PBP_0_0_3,
);

Readonly::Scalar my $EN_AU                       => 'en_AU';
Readonly::Scalar my $EN_US                       => 'en_US';
Readonly::Scalar my $ORIGINAL_MODULE_VERSION     => 'original';

Readonly::Hash my %SOURCE_DEFAULT_LANGUAGE     => (
    $BOOK_FIRST_EDITION => $ORIGINAL_MODULE_VERSION,
    $M_S_PBP_0_0_3      => $EN_AU,
);

Readonly::Scalar my $BOOK_FIRST_EDITION_US_LIB_SECTIONS =>
    [
        'NAME',
        'VERSION',
        'SYNOPSIS',
        'DESCRIPTION',
        'SUBROUTINES/METHODS',
        'DIAGNOSTICS',
        'CONFIGURATION AND ENVIRONMENT',
        'DEPENDENCIES',
        'INCOMPATIBILITIES',
        'BUGS AND LIMITATIONS',
        'AUTHOR',
        'LICENSE AND COPYRIGHT',
    ];

Readonly::Hash my %DEFAULT_LIB_SECTIONS => (
    $BOOK_FIRST_EDITION => {
        $ORIGINAL_MODULE_VERSION => $BOOK_FIRST_EDITION_US_LIB_SECTIONS,
        $EN_AU => [
            'NAME',
            'VERSION',
            'SYNOPSIS',
            'DESCRIPTION',
            'SUBROUTINES/METHODS',
            'DIAGNOSTICS',
            'CONFIGURATION AND ENVIRONMENT',
            'DEPENDENCIES',
            'INCOMPATIBILITIES',
            'BUGS AND LIMITATIONS',
            'AUTHOR',
            'LICENCE AND COPYRIGHT',
        ],
        $EN_US => $BOOK_FIRST_EDITION_US_LIB_SECTIONS,
    },
    $M_S_PBP_0_0_3 => {
        $EN_AU => [
            'NAME',
            'VERSION',
            'SYNOPSIS',
            'DESCRIPTION',
            'INTERFACE',
            'DIAGNOSTICS',
            'CONFIGURATION AND ENVIRONMENT',
            'DEPENDENCIES',
            'INCOMPATIBILITIES',
            'BUGS AND LIMITATIONS',
            'AUTHOR',
            'LICENCE AND COPYRIGHT',
            'DISCLAIMER OF WARRANTY',
        ],
        $EN_US => [
            'NAME',
            'VERSION',
            'SYNOPSIS',
            'DESCRIPTION',
            'INTERFACE',
            'DIAGNOSTICS',
            'CONFIGURATION AND ENVIRONMENT',
            'DEPENDENCIES',
            'INCOMPATIBILITIES',
            'BUGS AND LIMITATIONS',
            'AUTHOR',
            'LICENSE AND COPYRIGHT',
            'DISCLAIMER OF WARRANTY'
        ],
    },
);

Readonly::Hash my %DEFAULT_SCRIPT_SECTIONS => (
    $BOOK_FIRST_EDITION => {
        $ORIGINAL_MODULE_VERSION => [
            'NAME',
            'USAGE',
            'DESCRIPTION',
            'REQUIRED ARGUMENTS',
            'OPTIONS',
            'DIAGNOSTICS',
            'EXIT STATUS',
            'CONFIGURATION',
            'DEPENDENCIES',
            'INCOMPATIBILITIES',
            'BUGS AND LIMITATIONS',
            'AUTHOR',
            'LICENSE AND COPYRIGHT',
        ],
        $EN_AU => [
            'NAME',
            'VERSION',
            'USAGE',
            'REQUIRED ARGUMENTS',
            'OPTIONS',
            'DESCRIPTION',
            'DIAGNOSTICS',
            'CONFIGURATION AND ENVIRONMENT',
            'DEPENDENCIES',
            'INCOMPATIBILITIES',
            'BUGS AND LIMITATIONS',
            'AUTHOR',
            'LICENCE AND COPYRIGHT',
        ],
        $EN_US => [
            'NAME',
            'VERSION',
            'USAGE',
            'REQUIRED ARGUMENTS',
            'OPTIONS',
            'DESCRIPTION',
            'DIAGNOSTICS',
            'CONFIGURATION AND ENVIRONMENT',
            'DEPENDENCIES',
            'INCOMPATIBILITIES',
            'BUGS AND LIMITATIONS',
            'AUTHOR',
            'LICENSE AND COPYRIGHT',
        ],
    },
    $M_S_PBP_0_0_3 => {
        $EN_AU => [
            'NAME',
            'VERSION',
            'USAGE',
            'REQUIRED ARGUMENTS',
            'OPTIONS',
            'DESCRIPTION',
            'DIAGNOSTICS',
            'CONFIGURATION AND ENVIRONMENT',
            'DEPENDENCIES',
            'INCOMPATIBILITIES',
            'BUGS AND LIMITATIONS',
            'AUTHOR',
            'LICENCE AND COPYRIGHT',
            'DISCLAIMER OF WARRANTY',
        ],
        $EN_US => [
            'NAME',
            'VERSION',
            'USAGE',
            'REQUIRED ARGUMENTS',
            'OPTIONS',
            'DESCRIPTION',
            'DIAGNOSTICS',
            'CONFIGURATION AND ENVIRONMENT',
            'DEPENDENCIES',
            'INCOMPATIBILITIES',
            'BUGS AND LIMITATIONS',
            'AUTHOR',
            'LICENSE AND COPYRIGHT',
            'DISCLAIMER OF WARRANTY',
        ],
    },
);

#-----------------------------------------------------------------------------

sub supported_parameters {
    return qw( lib_sections script_sections source language )
}

sub default_severity { return $SEVERITY_LOW            }
sub default_themes   { return qw(core pbp maintenance) }
sub applies_to       { return 'PPI::Document'          }

#-----------------------------------------------------------------------------

sub initialize_if_enabled {
    my ($self, $config) = @_;

    # Set config, if defined
    for my $section_type ( qw(lib_sections script_sections) ) {
        if ( defined $config->{$section_type} ) {
            my @sections = split m{ \s* [|] \s* }mx, $config->{$section_type};
            @sections = map { uc $_ } @sections;  #Nomalize CaSe!
            $self->{ "_$section_type" } = \@sections;
        }
    }

    my $source = $config->{source};
    if ( not defined $source or not defined $DEFAULT_LIB_SECTIONS{$source} ) {
        $source = $DEFAULT_SOURCE;
    }

    my $language = $config->{language};
    if (
            not defined $language
        or  not defined $DEFAULT_LIB_SECTIONS{$source}{$language}
    ) {
        $language = $SOURCE_DEFAULT_LANGUAGE{$source};
    }

    if (not defined $self->{_lib_sections}) {
        $self->{_lib_sections} = $DEFAULT_LIB_SECTIONS{$source}{$language};
    }
    if (not defined $self->{_script_sections}) {
        $self->{_script_sections} =
            $DEFAULT_SCRIPT_SECTIONS{$source}{$language};
    }

    return $TRUE;
}

#-----------------------------------------------------------------------------

sub violates {
    my ( $self, $elem, $doc ) = @_;

    # This policy does not apply unless there is some real code in the
    # file.  For example, if this file is just pure POD, then
    # presumably this file is ancillary documentation and you can use
    # whatever headings you want.
    return if ! $doc->schild(0);

    my %found_sections = ();
    my @violations = ();

    my @required_sections = is_script($doc) ? @{ $self->{_script_sections} }
                                            : @{ $self->{_lib_sections} };

    my $pods_ref = $doc->find('PPI::Token::Pod');
    return if !$pods_ref;
    my $counter  = 0;  #Might use this to enforce ordering.

    # Round up the names of all the =head1 sections
    for my $pod ( @{ $pods_ref } ) {
        for my $found ( $pod =~ m{ ^ =head1 \s+ ( .+? ) \s* $ }gmx ) {
            #Leading/trailing whitespace is already removed
            $found_sections{ uc $found } = ++$counter;
        }
    }

    # Compare the required sections against those we found
    for my $required ( @required_sections ) {
        if ( ! exists $found_sections{$required} ) {
            my $desc = qq{Missing "$required" section in POD};
            push @violations, $self->violation( $desc, $EXPL, $doc );
        }
    }

    return @violations;
}

1;

__END__

#-----------------------------------------------------------------------------

=pod

=for stopwords licence

=head1 NAME

Perl::Critic::Policy::Documentation::RequirePodSections

=head1 DESCRIPTION

This Policy requires your POD to contain certain C<=head1> sections.
If the file doesn't contain any POD at all, then this Policy does not
apply.  Tools like L<Module::Starter> make it really easy to ensure
that every module has the same documentation framework, and they can
save you lots of keystrokes.

=head1 DEFAULTS

Different POD sections are required, depending on whether the file is
a library or program (which is determined by the presence or absence
of a perl shebang line).

             Default Required POD Sections

   Perl Libraries                     Perl Programs
   ------------------------------------------------------
   NAME                               NAME
   VERSION
   SYNOPSIS                           USAGE
   DESCRIPTION                        DESCRIPTION
   SUBROUTINES/METHODS                REQUIRED ARGUMENTS
                                      OPTIONS
   DIAGNOSTICS                        DIAGNOSTICS
                                      EXIT STATUS
   CONFIGURATION AND ENVIRONMENT      CONFIGURATION
   DEPENDENCIES                       DEPENDENCIES
   INCOMPATIBILITIES                  INCOMPATIBILITIES
   BUGS AND LIMITATIONS               BUGS AND LIMITATIONS
   AUTHOR                             AUTHOR
   LICENSE AND COPYRIGHT              LICENSE AND COPYRIGHT

=head1 CONFIGURATION

The default sections above are derived from Damian Conway's I<Perl
Best Practices> book.  Since the book has been published, Conway has
released L<Module::Starter::PBP>, which has different names for some
of the sections, and adds some more.  Also, the book and module use
Australian spelling, while the authors of this module have previously
used American spelling.  To sort this all out, there are a couple of
options that can be used: C<source> and C<language>.

The C<source> option has two generic values, C<book> and
C<module_starter_pbp>, and two version-specific values,
C<book_first_edition> and C<module_starter_pbp_0_0_3>.  Currently, the
generic values map to the corresponding version-specific values, but
may change as new versions of the book and module are released, so use
these if you want to keep up with the latest and greatest.  If you
want things to remain stable, use the version-specific values.

The C<language> option has a default, unnamed value but also accepts
values of C<en_AU> and C<en_US>.  The reason the unnamed value exists
is because the default values for programs don't actually match the
book, even taking spelling into account, i.e. C<CONFIGURATION> instead
of C<CONFIGURATION AND ENVIRONMENT>, the removal of C<VERSION>, and
the addition of C<EXIT STATUS>.  To get precisely the sections as
specified in the book, put the following in your F<.perlcriticrc>
file:

  [Documentation::RequirePodSections]
  source   = book_first_edition
  language = en_AU

If you want to use

  [Documentation::RequirePodSections]
  source   = module_starter_pbp
  language = en_US

you will need to modify your F<~/.module-starter/PBP/Module.pm>
template because it is generated using Australian spelling.

Presently, the difference between C<en_AU> and C<en_US> is in how the
word "licence" is spelled.

The sections required for modules and programs can be independently
customized, overriding any values for C<source> and C<language>, by
giving values for C<script_sections> and C<lib_sections> of a string
of pipe-delimited required POD section names.  An example of entries
in a F<.perlcriticrc> file:

  [Documentation::RequirePodSections]
  lib_sections    = NAME | SYNOPSIS | BUGS AND LIMITATIONS | AUTHOR
  script_sections = NAME | USAGE | OPTIONS | EXIT STATUS | AUTHOR

=head1 LIMITATIONS

Currently, this Policy does not look for the required POD sections
below the C<=head1> level.  Also, it does not require the sections to
appear in any particular order.

=head1 AUTHOR

Jeffrey Ryan Thalhammer <thaljef@cpan.org>

=head1 COPYRIGHT

Copyright (c) 2006 Jeffrey Ryan Thalhammer.  All rights reserved.

This program is free software; you can redistribute it and/or modify
it under the same terms as Perl itself.  The full text of this license
can be found in the LICENSE file included with this module

=cut

# Local Variables:
#   mode: cperl
#   cperl-indent-level: 4
#   fill-column: 78
#   indent-tabs-mode: nil
#   c-indentation-style: bsd
# End:
# ex: set ts=8 sts=4 sw=4 tw=78 ft=perl expandtab :
