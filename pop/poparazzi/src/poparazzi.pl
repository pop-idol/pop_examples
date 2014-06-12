#!/usr/bin/perl -w
#-------------------------------------------------------------------------------

=head1 poparazzi.pl

=cut

=head1 Synopsis

    This application is a sparse application.

    The program narrative begins in the MAIN block at the bottom of
    the file

=cut

#-------------------------------------------------------------------------------

=head3 File History

    1/1/1970  - MOA  - first implementation of the app.

=cut

#-------------------------------------------------------------------------------

=head3 Module Dependencies

    use strict;
    use warnings;
    use Getopt::Long;
    use Switch;
    use POP;

    use Poparazzi;

=cut

#-------------------------------------------------------------------------------

# only globals PLEASE!

our $true  = ( 1 == 1 );
our $false = ( 1 == 0 );

# loader section

use strict;
use warnings;
use Getopt::Long;
use Switch;
use POP;

use Poparazzi;

#-------------------------------------------------------------------------------

=head1 Subroutines

    The list of subroutines for this file

=cut

#-------------------------------------------------------------------------------

=head3 About POP Sparse Application Subroutines

    This is a sparse application file.  There is a fixed number of subroutines
    in any POP sparse application:

        1 print_usage($;);
        2 parse_commandline_arguments($;);
        3 init_local_data($;);
        4 the MAIN block

    All other subroutines are pulled in from external libraries (module files).

=cut

#-------------------------------------------------------------------------------

# POD TRICK:  if there is no space between the subroutine name and '(' the
# translator should print the name in courier new, otherwise it will treat  the
# name  as a normal head3 title. This is the only fancy POD in POP.

#-------------------------------------------------------------------------------

=head3 print_usage($;$)

    This prints the usage message and an optional error message  and exits;

    Example:

        print_usage($args_href, $msg);

=cut

#-------------------------------------------------------------------------------

sub print_usage ($;$) {

    my $sub = ( caller(0) )[3];

    my $args_href  = shift;
    my $msg        = shift;

    my $usage_str;

    if ( ! $args_href->{'help_arg'} ) {

       $usage_str = "

    usage: poparazzi [options] COMMAND

        ";

        $usage_str .= $msg if defined $msg;


        print "$usage_str\n\n";
        exit $false;
    }

}

#-------------------------------------------------------------------------------

=head3 parse_commandline_arguments($;)

    This routine parses the arguments to the application from the commandline.
    It should be the first subroutine called from MAIN.

    Usage:

        $args_href = parse_commandline_arguments ($args_href);

=cut

#-------------------------------------------------------------------------------

sub parse_commandline_arguments ($;) {

    my $sub = ( caller(0) )[3];
    trace_enter($sub);

    my $args_href = shift;

    my $arg_cnt = @ARGV;
    $args_href->{'arg_cnt'} = $arg_cnt;

    Getopt::Long::Configure("bundling");

    # parameter processing

 # Getopt tutorial:
 # "x|xls=s"  - will take a flag -x or --xls followed by a string ( -x string ).
 #            - and assign the sring to the variable (below)
 # "h|help"   - will take -h or --help as a flag  ( --help ).
 #            - and assign $true to a variable.

    my $result = GetOptions(

        "h|help"    => \$args_href->{'help_arg'},
        "t|trace"   => \$args_href->{'trace_arg'},
        "v|version" => \$args_href->{'version_arg'},

        # add more...
    );

    my $msg;
    # check for Getopt errors - $result is 1 on success
    if ( $result != 1 ) {
        $msg = "Unknown options argument";
        print_usage($args_href, $msg);
    }

    if ( $args_href->{'version_arg'} ) {
        return $args_href;
    }

    # set the valid command list here and add to args_href
    my @cmds_array =
      ( 'new.file.set', 'add.pkgs', 'add.subs', 'move.to.lib', 'check.pod' );
    $args_href->{'cmdlist_aref'} = \@cmds_array;

    # get the command.  Last element from the commandline
    my $cmd = $ARGV[$#ARGV];

    if ( !$cmd and $arg_cnt == 0 ) {
        $msg = "You need to supply a COMMAND";
        print_usage($args_href, $msg);
    }

    # check the cmd against the list of commands
    if ( $cmd and !grep( /^$cmd$/, @cmds_array ) ) {
        $msg = "Invalid COMMAND";
    }
    $args_href->{'cmd'} = lc $cmd;

    # trace argument
    $ENV{POP_TRACE} = $true if $args_href->{'trace_arg'};

    # help argument handled in get_local_data()

    # all options have been handled, but still need a cmd to proceed
    $msg = "You need to supply a COMMAND";
    print_usage($args_href, $msg) if ! $cmd;

    # always the only return value
    return $args_href;

}

#-------------------------------------------------------------------------------

=head3 init_local_data($;)

    This routine initializes values in the $args_href which are
    specific to this application and this invocation.

    This should be the last init routine called from the MAIN block .

    Usage:

        $args_href = init_local_data($args_href);

=cut

#-------------------------------------------------------------------------------

sub init_local_data ($;) {

    my $sub = ( caller(0) )[3];
    trace_enter($sub);

    my $args_href = shift;

    # some local data
    my $app_name = $args_href->{'short_app_name'};
    my $version  = "1.0";

    $args_href->{'version'}  = $version;
    $args_href->{'app_name'} = $app_name;

    if ( $args_href->{'version_arg'} ) {

        # print version information
        my $msg = "

             $app_name

             Version ($version)
             Copyright Man of Action 2014

        ";
        print "$msg\n";

        trace_exit($sub);
        exit 0;
    }

    if ( $args_href->{'help_arg'} ) {

        my $usage_str = $args_href->{'poparazzi_help_msg'};

        print "$usage_str\n";
    }

    trace_exit($sub);
    return $args_href;
}

#-------------------------------------------------------------------------------

=head3 MAIN()

    The main entry point to the application.

    This is where the Developer starts the POP program narrative for
    the Reader.

=cut

#-------------------------------------------------------------------------------

{    # MAIN main Main block

    my $sub =
      "MAIN";    # here, $sub is a literal string, since 'MAIN' is just a block
    trace_enter($sub);

    my $args_href;

    # initialize the shared data for the application

    $args_href = parse_commandline_arguments($args_href);    # parse arguments
    $args_href = poparazzi_init_common_data($args_href);     # module level init
    $args_href = init_local_data($args_href);                # app level init

    my $cmd = $args_href->{'cmd'};
    if ( !$cmd ) {
        print "ERROR:  Made it to MAIN with an empty cmd\n";
        exit;
    }

    #
    #   Start of the Narrative for the Reader
    #
    #

    # reusable local variables
    my ( $aref, $href, @array, $str );

    #
    # get the cmd_index of the command
    # cmds are ('new.file.set', 'add.pkgs', 'add.subs', 'movetolib','checkpod')
    #
    my $cmd_index = 0;
    $aref = $args_href->{'cmdlist_aref'};
    foreach my $cmd_str (@$aref) {
        last if ( $cmd_str eq $cmd );
        $cmd_index++;
    }

    #
    #   This is the main driver switch for handling commands
    #   from the commandline
    #

    switch ($cmd_index) {

        # new command
        case 0 { poparazzi_create_new_project($args_href) }

        # add.pkgs
        case 1 {
            my $code_href = poparazzi_add_pkgs_to_module_file($args_href);
            ref_dump($code_href);
        }

        # add.subs
        case 2 { poparazzi_add_subs_to_module_file($args_href) }

        # movetolib
        case 3 { poparazzi_move_subs_to_lib($args_href) }

        # checkpod
        case 4 { poparazzi_check_pod_headers($args_href) }

        # default
        else { print "Could not resolve command '$cmd'\n"; exit $false }

    }

    my $status = 0;

   #my $status = poparazzi_subroutine($args_href);    # call a Module subroutine

    if ( $status == 0 ) {

        # zero or empty string is equates to failure

        print "BACK to APP\n";
    }

    trace_exit($sub);
    exit $status;

}    # end of MAIN

#-------------------------------------------------------------------------------

=head1 ^

=cut

# EOF
