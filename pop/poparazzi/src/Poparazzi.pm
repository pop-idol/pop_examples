#!/usr/bin/perl -w 
# ------------------------------------------------------------

=head1 poparazzi.pm

     poparazzi.pm

     a utility for refactoring standard perl sources into the POP program style

=cut

# -------------------------------------------------------------------------------

=head3 File History


    Revision 1.0  2014/05/1  MoA
    Reviewers: none

    First implimentation of the script begun.


=cut

#-------------------------------------------------------------------------------

=head3 Module Dependencies

    use strict;
    use warnings;
    no warnings qw(void);
    use Data::Dumper;
    use Net::Telnet;
    use DBI;
    use Date::Parse;
    use POSIX 'strftime';
    use Storable 'dclone';

    use Parallel::ForkManager;
    use Fcntl ':flock'; # Import LOCK_* constants
    use IPC::ShareLite;
    use Tie::ShareLite qw( :lock );

    use Time::Local;
    use Time::HiRes qw(time);
    use UNIVERSAL 'isa';
    use Net::Ping;
    use LWP::UserAgent;
    use HTTP::Request;
    use XML::XPath;
    use XML::XPath::XMLParser;
    use Data::Dumper;
    use HTTP::Request::Common;
    use Date::Calc qw(Today_and_Now Add_Delta_DHMS);

=cut

# -------------------------------------------------------------------------------

# only globals PLEASE!

our $true  = ( 1 == 1 );
our $false = !$true;

# loader section

use strict;
use warnings;
no warnings qw(void);
use Data::Dumper;
use DBI;
use POSIX 'strftime';
use Storable 'dclone';
use Time::Local;
use Time::HiRes qw(time);
use UNIVERSAL 'isa';
use LWP::UserAgent;
use HTTP::Request;
use HTTP::Request::Common;
use Sys::Syslog;
use Sys::Syslog qw(:standard :macros);

#use Parallel::ForkManager;
use Fcntl ':flock';    # Import LOCK_* constants

#use IPC::ShareLite;
#use Tie::ShareLite qw( :lock );
#use XML::Hash;
#use Hash::Merge::Simple qw/ merge /;

# -------------------------------------------------------------------------------

=head1 Subroutines

=cut

# -------------------------------------------------------------------------------

#  POD trick:  if there is no space between the subroutine name and '(' the
#  translator should print the name in courior new, otherwise it will treat  the
#  name  as a normal titile. (works on centos5 at least)...

#------------------------------------------------------------------------------

=head2 ecut collector utility subroutines

=head3 poparazzi_init_common_data($;)

    Intializes the comman data for an application.  This is the central
    data repository for all POP-style applications.  This is where all
    shared data should be declared and initialized.  

    The data is held, by convention, in the hash reference $args_href.
    The $args_href is typically passed as the first argument to any
    routine that needs access to shared data, which is pretty common.

    The name $args_href comes from the fact that this hash is intialized
    based on the commandline arguments to the application.  The init
    process for POP-style apps is:

        1. parse commandline arguments
        2. initialize the shared data elements, based in part on the 
           commandline arguments and the runtime environment.
        3. inialize the local data.  This data are specific to the
           the imediate runtime environment and the specifics of the
           invocation of the app and is done in init_local_data() in
           the application file..

    Take Away: if you need a so-call "global" value, this is the place
               to put it and you access it using a syntax like:

                   $local_variable = $args_href->{'global_data_name'}
.

    Usage:

        $args_href = poparazzi_init_common_data ($args_href);

        Note that the $args_href is both the single input parameter and
        the single return value.  The $args_href should only be returned
        my init routines, never by a normal subroutine.

    Return:

        $args_href or exits on Error;

=cut

#-------------------------------------------------------------------------------

sub poparazzi_init_common_data ($;) {

    my $sub = ( caller(0) )[3];

    # trace_enter called farther down

    my $args_href = shift;

    # reusable working variables
    my ( $href, %hash, $aref, $string, $msg, $dnsname, $portname );

    # usually trace_enter is the first call in a subroutine
    # but that code is in the ecut library.
    trace_enter($sub);

    my $long_app_name = $0;
    chomp($long_app_name);
    my @parts = split( /\//, $long_app_name );
    my $short_app_name = $parts[$#parts];
    @parts = split( /\./, $short_app_name );
    my $app_name_str = $parts[0];

    $args_href->{'long_app_name'}  = $long_app_name;
    $args_href->{'short_app_name'} = $short_app_name;
    $args_href->{'app_name_str'}   = $app_name_str;

    # start the syslog interface
    #openlog( $short_app_name, "ndelay,pid", "local0" );

    my $lib_version = "";
    my $lib_date    = "";

    $args_href->{'lib_version'} = $lib_version;
    $args_href->{'lib_date'}    = $lib_date;

    #
    # just return if user wants app version information
    #
    return $args_href if $args_href->{'version_arg'};

    #
    # initialize shared data and add it to $args_href
    #
    # data comes from 'ini' and 'csv' files and
    # from the ECUT database or the commandline &
    # some data is assigned directly as scalars
    #

    # add some paths

    my $home = $ENV{HOME};
    $args_href->{'home_dir'} = $home;

    my $root = "/";
    $args_href->{'root_dir'} = $root;

    my $tmp_dir = $root . "/tmp";
    $args_href->{'tmp_dir'} = $tmp_dir;

    my $lib__dir = $root . "/lib";
    $args_href->{'lib__dir'} = $lib__dir;

    my $etc_dir = $root . "/etc";
    $args_href->{'etc_dir'} = $etc_dir;

    #
    # slurp config files into $args_href here
    #

    # the poparazzi config file in the user's HOME dir

    my $config_filename = "$home/.poparazzi.csv";
    if ( -e $config_filename ) {
        ( $href, $aref ) = pop_slurp_file_with_suffix($config_filename);
        foreach my $key (@$aref) {
            $args_href->{'defaults'}->{$key} = $href->{$key};
        }
    }
    $args_href->{'poparazzi_config_filename'} = $config_filename;

    # get the application name and remove .pl
    @parts = split( /\.pl/, $short_app_name );
    my $name_stub = $parts[0];

    #  this may need some tweaking

    my $timestamp = poparazzi_time_get_timestamp();
    my @array = split( " ", $timestamp );

    # year month day
    my $ymd = $array[0];

    # time of day
    my $tod = $array[1];

    # timezone
    my $tz = $array[2];

    # make a magnitude value for camparing time segments
    # in filenames from the controller boxes
    my ( $year, $month, $day ) = split( /-/, $ymd );
    my ( $hour, $min,   $sec ) = split( /:/, $tod );

    my $neg_hour = $hour - 1;
    $neg_hour = "0" . $neg_hour if $neg_hour < 10;
    my $time_interval_start = $year . $month . $day . $neg_hour . $min . $sec;
    my $time_interval_end   = $year . $month . $day . $hour . $min . $sec;

    # deal with change of day
    if ( $neg_hour == 0 ) {
        my $pos_day = $day + 1;
        $time_interval_start = $year . $month . $pos_day . "00" . $min . $sec;
    }

    $args_href->{'timestamp'} = $timestamp;
    $args_href->{'timezone'}  = $tz;
    $args_href->{'timezone'}  = $args_href->{'master_timezone'} if !$tz;

    #$args_href->{'time_magnitude'}      = $time_magnitude;
    $args_href->{'time_interval_start'} = $time_interval_start;
    $args_href->{'time_interval_end'}   = $time_interval_end;
    $args_href->{'date'}                = $ymd;
    $args_href->{'time_of_day'}         = $tod;
    $args_href->{'current_hour'}        = $hour;
    $args_href->{'current_year'}        = $year;

    # debug
    #print "timestamp: $timestamp\n";
    #print "timezne: $tz\n";
    #print "time_interval_start: $time_interval_start\n";
    #print "time_interval_end: $time_interval_end\n";
    #print "date: $ymd\n";
    #print "time_of_data: $tod\n";
    #print "current_hour: $hour\n";

    my $file_arg    = $args_href->{'file_arg'};
    my $list_arg    = $args_href->{'list_arg'};
    my $version_arg = $args_href->{'version_arg'};

    chomp $list_arg if $list_arg;
    chomp $file_arg if $file_arg;

    #
    #  Text blocks area
    #  large blocks of text that would complicate the Narative if they
    #  were are defined in-place.
    #

    #
    #  intro_to_new_project
    #

    $args_href->{'intro_to_new_project'} = "

    The 'new.file.set' command

    The 'new.file.set' command will create POP project files. It will
    create an application level (.pl) file and a program module (.pm) file.
    It will also make a preparation file, 'prep.sh' to simplify formatting
    the script with perltidy and for creating publishable POD documentation.

    The tool will ask you for the following details:

       - Name - The name of the Application (not the file names).
       - Author - The name of the Author of the script.  
       - Organization - The name of the Company paying for the script.  

    Once it has this information the tool will go off and create the
    \.pl,  \.pm  and prep files with proper POD sections and ordered
    as recommened by the POP style.

    The preparation file, 'prep.sh' is included to simplify formatting the
    the Perl files with perltidy and for creating publishable POD
    documentation.

    ";

    #
    #  intro_to_add_pkgs
    #

    $args_href->{'intro_to_add_pkgs'} = "

    The 'add.pkgs' command

    This usecase eases the task of adding program module 'use' 
    statements to a module\.pm file.

    The 'add.pkgs' command will add CPAN and home-grown modules 'use' 
    statements to a POP module file.

    The changes will be added to a file named <module_file\.pm>\.POP
    not to the original \.pm file.

    The tool will ask you for the following details:

      - Moduel file name - the module \.pm filename to change.
      - Package list - a space separated list of Packages to add.

    Once you have entered this information the tool will go off and 
    add 'use' statements for each package in the package list. 

    The changes will be added to a temporary <module\.pm>\.POP file not
    to the original <module\.pm> file..

    Once processing is done you should look over the module\.pm.\.POP
    file and rename it to the original module.pm filename to save the
    changes.

    ";

    #
    #  intro_to_add_subs
    #
    $args_href->{'intro_to_add_subs'} = "

    The 'add.subs' command

    This usecase eases the task of adding new subroutines to Perl module files.

    The 'add.subs' command will create new subroutine templates in a module\.pm file.
    It will add the subroutines to the selected file in alphabetical order.

    The changes will be added to a temporary <module\.pm>\.POP file not the
    original <module.pm> file.

    The tool will ask you for the following details:

       - module file name - The name of the <module.pm> file to add subroutines
       - subroutine list -  A space separated list of subroutine names to add
      
    Once you have entered this information the tool will go off and 
    add the subroutine template stubs to the a temporary copy of the original file.

    Once processing is done you must look over the resulting temp file.
    Then rename the \. POP file to the original filename if all looks OK.

    ";

    $args_href->{'poparazzi_help_msg'} = "

Usage: poparazzi [options] COMMAND

List of Commands:

new.file.set   Creates a .pm, .pl and prep.sh files for an application
add.pkgs       Adds use statements from a package list to a temporary module file
add.subs       Adds template subroutines to a temporary module file

Options:
  -h, --help            show this help message and exit
  -v, --version         show Yum version and exit
  -t, --trace           execute script, printing trace information 

    ";

    #
    # done with shared data initialization
    # return to Main block
    #

    trace_exit($sub);
    return $args_href;    # always the only return value
}

# -----------------------------------------------------------------------------------------------------

=head3 poparazzi_add_pkgs_to_module_file($;)

     Add CPAN and other packages to a POP pm file

     Usage: 

        my $status = poparazzi_add_pkgs_to_module_file( $args_href );

=cut

#-----------------------------------------------------------------------------------------------------

sub poparazzi_add_pkgs_to_module_file($;) {

    my $sub = ( caller(0) )[3];
    trace_enter($sub);

    my $args_href = shift;

    # reusable variable names
    my ( $dialog_href, $msg, $response, $str, $status, $default, @array );

    # the gathered data variables
    my ( $mod_filename, $pkg_list, $author, $organization, $stub_count,
        $stub_list );

    my $intro = $args_href->{'intro_to_add_pkgs'};
    $msg =
      "Do you want to add module 'use' statements to a module file (y\/n)?";
    $default = "n";

    $response = poparazzi_dialog_start( $intro, $msg, $default );
    return $false if $response eq "n" or $response eq "no";

    $msg      = "Enter the full Module Filename including \.pm suffix";
    $default  = $args_href->{'defaults'}->{'mod_filename'};
    $response = poparazzi_dialog_continue( $msg, $default );

    while ( !$response or $response eq "" ) {

        $msg      = "You need to enter a filename string. (CTRL-C to exit)";
        $response = poparazzi_dialog_continue($msg);
    }

    $mod_filename                  = lc $response;
    $mod_filename                  = ucfirst($mod_filename);
    $dialog_href->{'mod_filename'} = $mod_filename;

    if ( !-e $mod_filename ) {
        $msg = "$mod_filename not found";
        print "FATAL $sub: $msg\n";
        exit 0;
    }

    $msg     = "Enter a space separated list of pkg names";
    $default = $args_href->{'defaults'}->{'pkg_list'};

    $response                  = poparazzi_dialog_continue( $msg, $default );
    $pkg_list                  = $response;
    $dialog_href->{'pkg_list'} = $response;

    #
    #    print out the gathered data and get user buy-in
    #

    print "\n";
    print "    Here are the values you have entered:";
    print "\n";
    print "        Module File name:  $dialog_href->{'mod_filename'}\n";
    print "        Pkg list:          $dialog_href->{'pkg_list'}\n"
      if $dialog_href->{'pkg_list'};
    print "\n";

    $msg      = "Do you want continue using these values (yes or no )?";
    $response = poparazzi_dialog_continue($msg);

    while ( $response ne 'yes' and $response ne 'no' ) {

        $msg      = "You need to enter yes or no";
        $response = poparazzi_dialog_continue($msg);
    }

    if ( $response eq 'no' ) {
        trace_exit($sub);
        return $false;
    }

    # save the default values to the config file
    # for future calls to the tool

    my $config_filename = $args_href->{'poparazzi_config_filename'};
    my $config_fh       = pop_create_w_filehandle($config_filename);

    foreach my $key ( keys %$dialog_href ) {
        my $val = $dialog_href->{$key};
        print $config_fh "$key,$val\n";
    }
    close($config_fh);

    # time to make the the temporary .POP file

    $status =
      poparazzi_insert_use_statements_to_module_file( $args_href,
        $dialog_href );

    trace_exit($sub);
    return $status;
}

# -----------------------------------------------------------------------------------------------------

=head3 poparazzi_add_subs_to_module_file($;)

     Add new subroutine stubs to a POP pm file

     Usage: 

        my $status = poparazzi_add_subs_to_module_file( $args_href );

=cut

#-----------------------------------------------------------------------------------------------------

sub poparazzi_add_subs_to_module_file($;) {

    my $sub = ( caller(0) )[3];
    trace_enter($sub);

    my $args_href = shift;

    # reusable variable names
    my ( $dialog_href, $msg, $response, $str, $status, $default, @array );

    # the gathered data variables
    my (
        $mod_filename, $sub_list_str, $author,
        $organization, $stub_count,   $stub_list
    );

    my $intro = $args_href->{'intro_to_add_subs'};
    $msg     = "Do you want to add new subroutines to a module file (y\/n)?";
    $default = "n";

    $response = poparazzi_dialog_start( $intro, $msg, $default );
    return $false if $response eq "n" or $response eq "no";

    $msg      = "Enter the full Module Filename including \.pm suffix";
    $default  = $args_href->{'defaults'}->{'mod_filename'};
    $response = poparazzi_dialog_continue( $msg, $default );

    while ( !$response or $response eq "" ) {

        $msg      = "You need to enter a filename string. (CTRL-C to exit)";
        $response = poparazzi_dialog_continue($msg);
    }

    $mod_filename                  = lc $response;
    $mod_filename                  = ucfirst($mod_filename);
    $dialog_href->{'mod_filename'} = $mod_filename;

    if ( !-e $mod_filename ) {
        $msg = "$mod_filename not found";
        print "FATAL $sub: $msg\n";
        exit 0;
    }

    $msg     = "Enter a space separated list of subroutine names to add";
    $default = $args_href->{'defaults'}->{'sub_list_str'};

    $response = poparazzi_dialog_continue( $msg, $default );
    $sub_list_str = $response;
    $dialog_href->{'sub_list_str'} = $response;

    #
    #    print out the gathered data and get user buy-in
    #

    print "\n";
    print "    Here are the values you have entered:";
    print "\n";
    print "        Module File name:  $dialog_href->{'mod_filename'}\n";
    print "        Pkg list:          $dialog_href->{'sub_list_str'}\n"
      if $dialog_href->{'sub_list_str'};
    print "\n";

    $msg      = "Do you want continue using these values (yes or no )?";
    $response = poparazzi_dialog_continue($msg);

    while ( $response ne 'yes' and $response ne 'no' ) {

        $msg      = "You need to enter yes or no";
        $response = poparazzi_dialog_continue($msg);
    }

    if ( $response eq 'no' ) {
        trace_exit($sub);
        return $false;
    }

    # save the default values to the config file
    # for future calls to the tool

    my $config_filename = $args_href->{'poparazzi_config_filename'};
    my $config_fh       = pop_create_w_filehandle($config_filename);

    foreach my $key ( keys %$dialog_href ) {
        my $val = $dialog_href->{$key};
        print $config_fh "$key,$val\n";
    }
    close($config_fh);

    # time to make the the temporary .POP file

    $status =
      poparazzi_insert_subroutines_to_module_file( $args_href, $dialog_href );

    trace_exit($sub);
    return $status;
}

# -----------------------------------------------------------------------------------------------------

=head3 poparazzi_check_redundant_entries($;)

     Given a list of an array it will determine redundancy based from the HR timestamp
     Hence, at any given time there will be one entry PER HOUR to
     database.  This effort is to minimize the load of the database
     server.

     Usage: 

        my $aref2 = poparazzi_check_redundant_entries( $aref ));
        my @array2= @$aref2;

=cut

#-----------------------------------------------------------------------------------------------------

sub poparazzi_check_redundant_entries($;) {

    my $sub = ( caller(0) )[3];
    trace_enter($sub);

    my $ref_list = shift;

    my @newlist;
    my @hr_list;
    my $hr_last = 0;
    my $hr;
    my $index = 0;
    my $len   = scalar(@$ref_list);

    if ( !$len ) {
        print "Warning !!! Passing parameter is EMPTY.\n";
        return 0;
    }
    foreach my $line (@$ref_list) {
        chomp($line);

        # print "line = $line\n";
        $hr = poparazzi_time_get_hour_from_timestamp($line);
        if ( $index == 0 ) {
            push( @hr_list, $hr );
            push( @newlist, $line );

            #print "This is unique hr_list[$hr] vs line_list[@newlist]]\n";
        }

        #if ($hr != $hr_last)
        if ( grep /$hr/, @hr_list ) {

            #print "This is redundant [$hr vs [@hr_list]]\n";
        }
        else {
            #print "This is unique [$hr vs [@hr_list]]\n";
            push( @newlist, $line );
            push( @hr_list, $hr );
        }
        $index++;
    }

    trace_exit($sub);
    return (@newlist);
}

#-----------------------------------------------------------------------------------------------------

=head3 poparazzi_clobber_whitespace($;)

    Removes all whitespace from a string 
    a bit over done, should be cleaned up

=cut

#-----------------------------------------------------------------------------------------------------

sub poparazzi_clobber_whitespace ($;) {

    my $string = shift;

    $string =~ s/ //g;
    $string =~ s/\s+//g;
    $string =~ /\s*(\w+\s+=\s+\w+\s+|\w+\s+=\s+".*?"|\w+\s+=\s+<.*?>)\s*/g;
    $string =~ s/^\s+//;
    $string =~ s/\s+$//;
    $string =~ s/^\s+//;
    $string =~ s/\s+$//;

    $string = poparazzi_trim_left($string);
    $string = poparazzi_trim_right($string);
    $string = poparazzi_trim($string);

    return $string;
}

#-----------------------------------------------------------------------------------------------------

=head3 poparazzi_create_pop_module_file ($$;)

    Desc:        Creates a new program module file from an internal template

    Parameters : $args_href, $dialog_href
    Return     :  $true or $false

    Usage:

        my $status = 
            poparazzi_create_pop_module_file ( $args_href, $dialog_href );


=cut

#-----------------------------------------------------------------------------------------------------

sub poparazzi_create_pop_module_file ( $$;) {

    my $sub = ( caller(0) )[3];
    trace_enter($sub);

    my $args_href   = shift;
    my $dialog_href = shift;

    my $app_name     = $dialog_href->{'app_name'};
    my $app_filename = $dialog_href->{'app_filename'};
    my $mod_name     = $dialog_href->{'mod_name'};
    my $mod_filename = $dialog_href->{'mod_filename'};
    my $organization = $dialog_href->{'organization'};
    my $author       = $dialog_href->{'author'};

    my $date = $args_href->{'date'};

    # reusable variables
    my ( $i, $msg, $response, $aref, $href, $str, @array );

    if ( -e $mod_filename ) {

        $msg = "overwrite $mod_filename  (y\/n)?";
        $response = poparazzi_dialog_continue( $msg, 'n' );

        if ( $response eq 'n' ) {
            trace_exit($sub);
            return $true;
        }
    }

    # setup the output file handle
    my $pm_fh = pop_create_w_filehandle($mod_filename);

    #
    #   Write the template to the output file
    #

    print $pm_fh
"#-------------------------------------------------------------------------------\n";
    print $pm_fh "\n";
    print $pm_fh "=head1 $mod_filename\n";
    print $pm_fh "\n";
    print $pm_fh "=cut\n";
    print $pm_fh "\n";
    print $pm_fh "=head1 Synopsis\n";
    print $pm_fh "\n";
    print $pm_fh "#    TODO\n";
    print $pm_fh "\n";
    print $pm_fh "    Usage:\n";
    print $pm_fh "\n";
    print $pm_fh "        use $mod_name;\n";
    print $pm_fh "\n";
    print $pm_fh "=cut\n";
    print $pm_fh "\n";
    print $pm_fh
"#-------------------------------------------------------------------------------\n";
    print $pm_fh "\n";
    print $pm_fh "=head3 File History\n";
    print $pm_fh "\n";
    print $pm_fh "    $date  - $author - file created by poparazzi.\n";
    print $pm_fh "\n";
    print $pm_fh "=cut\n";
    print $pm_fh "\n";
    print $pm_fh
"#-------------------------------------------------------------------------------\n";
    print $pm_fh "\n";
    print $pm_fh "=head3 Module Dependencies\n";
    print $pm_fh "\n";
    print $pm_fh "    use strict\n";
    print $pm_fh "    use warnings\n";
    print $pm_fh "    use $mod_name\n";
    print $pm_fh "\n";
    print $pm_fh "    use POP:\n";
    print $pm_fh "\n";
    print $pm_fh "=cut\n";
    print $pm_fh "\n";
    print $pm_fh
"#-------------------------------------------------------------------------------\n";
    print $pm_fh "\n";
    print $pm_fh "# only globals PLEASE!\n";
    print $pm_fh "\n";
    print $pm_fh "our \$true  = ( 1 == 1 );\n";
    print $pm_fh "our \$false = ( 1 == 0 );\n";
    print $pm_fh "\n";
    print $pm_fh "# loader section\n";
    print $pm_fh "\n";
    print $pm_fh "use strict;\n";
    print $pm_fh "use warnings;\n";
    print $pm_fh "\n";
    print $pm_fh "use $mod_name;\n";
    print $pm_fh "\n";
    print $pm_fh "use POP;\n";
    print $pm_fh "\n";
    print $pm_fh
"#-------------------------------------------------------------------------------\n";
    print $pm_fh "\n";
    print $pm_fh "=head1 Subroutines\n";
    print $pm_fh "\n";
    print $pm_fh "=cut\n";
    print $pm_fh "\n";
    print $pm_fh
"#-------------------------------------------------------------------------------\n";
    print $pm_fh "\n";
    print $pm_fh
"# POD trick:  if there is no space between the subroutine name and '(' the\n";
    print $pm_fh
"# translator should print the name in courior new, otherwise it will treat  the\n";
    print $pm_fh "# name  as a normal titile. (works on centos5 at least)...\n";
    print $pm_fh "\n";
    print $pm_fh
"#-------------------------------------------------------------------------------\n";
    print $pm_fh "\n";
    print $pm_fh "=head3 " . $app_name . "_init_common_data(\$;)\n";
    print $pm_fh "\n";
    print $pm_fh "    Purpose:\n";
    print $pm_fh "\n";
    print $pm_fh "    This subroutine initializes the runime context for the\n";
    print $pm_fh "    $app_name application.\n";
    print $pm_fh "\n";
    print $pm_fh "    Usage:\n";
    print $pm_fh "\n";
    print $pm_fh "        \$args_href = "
      . $app_name
      . "_init_common_data (\$args_href);\n";
    print $pm_fh "\n";
    print $pm_fh "    Return:\n";
    print $pm_fh "\n";
    print $pm_fh "        \$args_href;\n";
    print $pm_fh "\n";
    print $pm_fh "\n";
    print $pm_fh "=cut\n";
    print $pm_fh "\n";
    print $pm_fh
"#-------------------------------------------------------------------------------\n";
    print $pm_fh "\n";
    print $pm_fh "sub " . $app_name . "_init_common_data (\$;) {\n";
    print $pm_fh "\n";
    print $pm_fh "    my \$sub = ( caller(0) )[3];\n";
    print $pm_fh "    trace_enter(\$sub);\n";
    print $pm_fh "\n";
    print $pm_fh "    my \$args_href = shift;\n";
    print $pm_fh "\n";
    print $pm_fh "    # initializes shared data\n";
    print $pm_fh "\n";
    print $pm_fh "    \$args_href->{\'library_version\'} = 1.0;;\n";
    print $pm_fh
      "    \$args_href->{\'library_name\'}    = \"$mod_filename\";\n";
    print $pm_fh "\n";
    print $pm_fh "    trace_exit(\$sub);\n";
    print $pm_fh "    return \$args_href;    # always the only return value\n";
    print $pm_fh "}\n";
    print $pm_fh "\n";

  # add requested subroutines and stubbs
  #    foreach my $sub_name (@stub_array) {
  #
  #        poparazzi_write_new_subroutine_block( $pm_fh, $app_name, $sub_name );
  #    }

    print $pm_fh
"#-------------------------------------------------------------------------------\n";
    print $pm_fh "\n";
    print $pm_fh "=head1 ^\n";
    print $pm_fh "\n";
    print $pm_fh "=cut\n";
    print $pm_fh "\n";
    print $pm_fh "1;    # always the last line in any Perl module file\n";

    close($pm_fh);

    trace_exit($sub);
    return $true;
}

#-----------------------------------------------------------------------------------------------------

=head3 poparazzi_create_pop_prep_file($$;)

    Desc:      Creates a POP prep.sh file for a project file set.

    Parameters : $args_href, $dialog_href
    Return     : $status

    Usage:

            my $status = 
               poparazzi_create_pop_prep_file ( $args_href, $dialog_href );

=cut

#-----------------------------------------------------------------------------------------------------

sub poparazzi_create_pop_prep_file($$;) {

    my $sub = ( caller(0) )[3];
    trace_enter($sub);

    my $args_href   = shift;
    my $dialog_href = shift;

    my $year = $args_href->{'current_year'};
    my $date = $args_href->{'date'};

    my $app_name      = $dialog_href->{'app_name'};
    my $app_filename  = $dialog_href->{'app_filename'};
    my $mod_name      = $dialog_href->{'mod_name'};
    my $mod_filename  = $dialog_href->{'mod_filename'};
    my $prep_filename = $dialog_href->{'prep_filename'};

    my ( $msg, $response );

    if ( -e $prep_filename ) {

        $msg = "overwrite $prep_filename  (y\/n)?";
        $response = poparazzi_dialog_continue( $msg, 'n' );

        if ( $response eq 'n' ) {

            trace_exit($sub);
            return $true;
        }
    }

    my $prep_fh = pop_create_w_filehandle($prep_filename);

    #
    #  print the template to the file
    #

    print $prep_fh "#!\/bin\/sh\n";
    print $prep_fh "\n";
    print $prep_fh "#         preparation script for $app_name\n";
    print $prep_fh "\n";
    print $prep_fh "# run files through formatter\n";
    print $prep_fh "\n";
    print $prep_fh "perltidy $app_filename\n";
    print $prep_fh "mv $app_filename.tdy $app_filename\n";
    print $prep_fh "\n";
    print $prep_fh "perltidy $mod_filename\n";
    print $prep_fh "mv $mod_filename.tdy $mod_filename\n";
    print $prep_fh "\n";
    print $prep_fh "perltidy POP.pm\n";
    print $prep_fh "mv POP.pm.tdy POP.pm\n";
    print $prep_fh "\n";
    print $prep_fh "# generate documentation html files\n";
    print $prep_fh "\n";
    print $prep_fh
"/usr/bin/pod2html --title \"$app_filename\" $app_filename  > docs/$app_filename.html\n";
    print $prep_fh
"/usr/bin/pod2html --title \"$mod_filename\" $mod_filename  > docs/$mod_filename.html\n";
    print $prep_fh
      "/usr/bin/pod2html --title \"POP.pm\" POP.pm > docs/POP.pm.html\n";
    print $prep_fh "\n";
    print $prep_fh "\n";
    print $prep_fh "# cleanup\n";
    print $prep_fh "\n";
    print $prep_fh "rm pod2htm*.tmp\n";
    print $prep_fh "\n";

    close($prep_fh);

    trace_exit($sub);
    return $true;
}

#-----------------------------------------------------------------------------------------------------

=head3 poparazzi_create_sparse_application_file($$;)

    Desc:      Creates a sparse application file based on the params.

    Parameters : $args_href, $dialog_href
    Return     : $status

    Usage:

            my $status = 
               poparazzi_create_sparse_application_file ( $args_href, $dialog_href );

       

=cut

#-----------------------------------------------------------------------------------------------------

sub poparazzi_create_sparse_application_file($$;) {

    my $sub = ( caller(0) )[3];
    trace_enter($sub);

    my $args_href   = shift;
    my $dialog_href = shift;

    my $year = $args_href->{'current_year'};
    my $date = $args_href->{'date'};

    my $app_name     = $dialog_href->{'app_name'};
    my $app_filename = $dialog_href->{'app_filename'};
    my $mod_name     = $dialog_href->{'mod_name'};
    my $mod_filename = $dialog_href->{'mod_filename'};

    my $organization = $dialog_href->{'organization'};
    my $author       = $dialog_href->{'author'};

    $app_filename = lc $app_filename;

    my ( $msg, $response );

    if ( -e $app_filename ) {

        $msg = "overwrite $app_filename  (y\/n)?";
        $response = poparazzi_dialog_continue( $msg, 'n' );

        if ( $response eq 'n' ) {

            trace_exit($sub);
            return $true;
        }
    }

    my $app_fh = pop_create_w_filehandle($app_filename);

    #
    #  print the template to the file
    #

    print $app_fh "#!/usr/bin/perl -w\n";
    print $app_fh
"#-------------------------------------------------------------------------------\n";
    print $app_fh "\n";
    print $app_fh "=head1 $app_name.pl\n";
    print $app_fh "\n";
    print $app_fh "=cut\n";
    print $app_fh "\n";
    print $app_fh "=head1 Synopsis  $app_name\n";
    print $app_fh "\n";
    print $app_fh "    This is a sparse application in the POP style.\n";
    print $app_fh "    The Program Narrative begins in the MAIN block at\n";
    print $app_fh "    the bottom of the file\n";
    print $app_fh "\n";
    print $app_fh "    The purpose of this application is:  TODO\n";
    print $app_fh "\n";
    print $app_fh "=cut\n";
    print $app_fh "\n";
    print $app_fh
"#-------------------------------------------------------------------------------\n";
    print $app_fh "\n";
    print $app_fh "=head3 File History\n";
    print $app_fh "\n";
    print $app_fh
      "    $date - $author - created application and library with poparazzi.\n";
    print $app_fh "\n";
    print $app_fh "=cut\n";
    print $app_fh "\n";
    print $app_fh
"#-------------------------------------------------------------------------------\n";
    print $app_fh "\n";
    print $app_fh "=head3 Module Dependencies\n";
    print $app_fh "\n";
    print $app_fh "    use strict;\n";
    print $app_fh "    use warnings;\n";
    print $app_fh "    use Getopt::Long;\n";
    print $app_fh "\n";
    print $app_fh "    use $mod_name;\n";
    print $app_fh "\n";
    print $app_fh "    use POP;\n";
    print $app_fh "\n";
    print $app_fh "=cut\n";
    print $app_fh "\n";
    print $app_fh
"#-------------------------------------------------------------------------------\n";
    print $app_fh "\n";
    print $app_fh "# No globals PLEASE!\n";
    print $app_fh "\n";
    print $app_fh "\n";
    print $app_fh "# loader section\n";
    print $app_fh "\n";
    print $app_fh "use strict;\n";
    print $app_fh "use warnings;\n";
    print $app_fh "use Getopt::Long;\n";
    print $app_fh "\n";

    #foreach my $pkg (@pkg_array) {
    #    print $app_fh "use $pkg;\n";
    #}

    print $app_fh "\n";
    print $app_fh "use POP;\n";
    print $app_fh "use $mod_name;\n";
    print $app_fh "\n";
    print $app_fh "# the only Globals Please \n";
    print $app_fh " \n";
    print $app_fh "my \$true  = ( 1 == 1 );\n";
    print $app_fh "my \$false = ! $true;\n";

    #print $app_fh "my \$false = \!\$true;\n";
    print $app_fh "\n";

    print $app_fh
"#-------------------------------------------------------------------------------\n";
    print $app_fh "\n";
    print $app_fh "=head1 Subroutines\n";
    print $app_fh "\n";
    print $app_fh "    The list of subroutines for this file\n";
    print $app_fh "\n";
    print $app_fh "=cut\n";
    print $app_fh "\n";
    print $app_fh
"#-------------------------------------------------------------------------------\n";
    print $app_fh "\n";
    print $app_fh "=head3 About POP Sparse Application Subroutines\n";
    print $app_fh "\n";
    print $app_fh
"    This is a sparse application file.  There is a fixed number of subroutines\n";
    print $app_fh "    in any POP sparse application:\n";
    print $app_fh "\n";
    print $app_fh "        1 print_usage(\$;);\n";
    print $app_fh "        2 parse_commandline_arguments(\$;);\n";
    print $app_fh "        3 init_local_data(\$;);\n";
    print $app_fh "        4 the MAIN block\n";
    print $app_fh "\n";
    print $app_fh
"    All other subroutines are pulled in from external libraries (module files).\n";
    print $app_fh "\n";
    print $app_fh "=cut\n";
    print $app_fh "\n";
    print $app_fh
"#-------------------------------------------------------------------------------\n";
    print $app_fh "\n";
    print $app_fh
"# POD TRICK:  if there is no space between the subroutine name and \'(\' the\n";
    print $app_fh
"# translator should print the name in courier new, otherwise it will treat  the\n";
    print $app_fh
      "# name  as a normal head3 title. This is the only fancy POD in POP.\n";
    print $app_fh "\n";
    print $app_fh
"#-------------------------------------------------------------------------------\n";
    print $app_fh "\n";

    print $app_fh "=head3 print_usage(\$;)\n";
    print $app_fh "\n";
    print $app_fh
"    This prints the usage message and an optional error message  and exits;\n";
    print $app_fh "\n";
    print $app_fh "    Example:\n";
    print $app_fh "\n";
    print $app_fh "        print_usage(\$msg);\n";
    print $app_fh "\n";
    print $app_fh "=cut\n";
    print $app_fh "\n";
    print $app_fh
"#-------------------------------------------------------------------------------\n";
    print $app_fh "\n";
    print $app_fh "sub print_usage (;\$) {\n";
    print $app_fh "\n";
    print $app_fh "    my \$sub = ( caller(0) )[3];\n";
    print $app_fh "    trace_enter(\$sub);\n";
    print $app_fh "\n";
    print $app_fh "    my \$msg = shift;\n";
    print $app_fh "\n";
    print $app_fh
      "    # a simple intuitive  way to print multi-line messages\n";
    print $app_fh "    my \$usage_str = \"\n";
    print $app_fh "\n";
    print $app_fh
      "    usage:  $app_name [-t|--trace] [-h|--help] [-v|--version]\n";
    print $app_fh "\";\n";
    print $app_fh "\n";
    print $app_fh "\n";
    print $app_fh
      "    # append optional msg argument to end of usage message\n";
    print $app_fh "    # best if message is last string printed to screen\n";
    print $app_fh "\n";
    print $app_fh "    \$usage_str .= \$msg if defined \$msg;\n";
    print $app_fh "\n";
    print $app_fh "    print \"\$usage_str\\n\\n\"; \n";
    print $app_fh "\n";
    print $app_fh "    exit \$false;\n";
    print $app_fh "}\n";
    print $app_fh "\n";

    print $app_fh
"#-------------------------------------------------------------------------------\n";
    print $app_fh "\n";
    print $app_fh "=head3 parse_commandline_arguments(\$;)\n";
    print $app_fh "\n";
    print $app_fh
"    This routine parses the arguments to the application from the commandline.\n";
    print $app_fh "    It should be the first subroutine called from MAIN.\n";
    print $app_fh "\n";
    print $app_fh "    Usage:\n";
    print $app_fh "\n";
    print $app_fh
      "        \$args_href = parse_commandline_arguments (\$args_href);\n";
    print $app_fh "\n";
    print $app_fh "=cut\n";
    print $app_fh "\n";
    print $app_fh
"#-------------------------------------------------------------------------------\n";
    print $app_fh "\n";
    print $app_fh "sub parse_commandline_arguments (\$;) {\n";
    print $app_fh "\n";
    print $app_fh "    my \$sub = ( caller(0) )[3];\n";
    print $app_fh "    trace_enter(\$sub);\n";
    print $app_fh "\n";
    print $app_fh "    my \$args_href = shift;\n";
    print $app_fh "\n";
    print $app_fh "    my \$arg_cnt = \@ARGV;\n";
    print $app_fh "    \$args_href->{\'arg_cnt\'} = \$arg_cnt;\n";
    print $app_fh "\n";
    print $app_fh "    Getopt::Long::Configure(\"bundling\");\n";
    print $app_fh "\n";
    print $app_fh "    # parameter processing\n";
    print $app_fh "\n";
    print $app_fh "    # Getopt tutorial:\n";
    print $app_fh
"    # \"x|xls=s\"  - will take a flag -x or --xls followed by a string ( -x string ).\n";
    print $app_fh
      "    #            - and assign the sring to the variable (below)\n";
    print $app_fh
      "    # \"h|help\"   - will take -h or --help as a flag  ( --help ).\n";
    print $app_fh "    #            - and assign \$true to a variable.\n";
    print $app_fh "\n";
    print $app_fh "    my \$result = GetOptions(\n";
    print $app_fh "\n";
    print $app_fh "        \"h\|help\"    => \\\$args_href->{\'help_arg\'},\n";
    print $app_fh "        \"t|trace\"   => \\\$args_href->{\'trace_arg\'},\n";
    print $app_fh
      "        \"v|version\" => \\\$args_href->{\'version_arg\'},\n";
    print $app_fh "\n";
    print $app_fh "        # more...\n";
    print $app_fh "    );\n";
    print $app_fh "\n";
    print $app_fh "    # check for Getopt errors - \$result is 1 on success\n";
    print $app_fh "    if ( \$result != 1 ) {\n";
    print $app_fh "        my \$msg = \"ERROR:  Unknown arguments\";\n";
    print $app_fh "        print_usage(\$msg);\n";
    print $app_fh "    }\n";
    print $app_fh "\n";
    print $app_fh
      "    # return \$args_href if there are no arguments on commandline\n";
    print $app_fh
      "    # this is uncommon -  invoking an application with no args\n";
    print $app_fh
      "    # usually means you should print the usage message and exit.\n";
    print $app_fh "\n";
    print $app_fh "    # return if no arguments\n";
    print $app_fh "    if ( \$arg_cnt == 0 ) { return \$args_href; }\n";
    print $app_fh "\n";
    print $app_fh "    # trace argument\n";
    print $app_fh
      "    \$ENV{POP_TRACE} = \$true if \$args_href->{\'trace_arg\'};\n";
    print $app_fh "\n";
    print $app_fh "    # help argument\n";
    print $app_fh "    print_usage() if \$args_href->{\'help_arg\'};\n";
    print $app_fh "\n";
    print $app_fh "    # always the only return value\n";
    print $app_fh "    return \$args_href;\n";
    print $app_fh "\n";
    print $app_fh "}\n";
    print $app_fh "\n";

    print $app_fh
"#-------------------------------------------------------------------------------\n";
    print $app_fh "\n";
    print $app_fh "=head3 init_local_data(\$;)\n";
    print $app_fh "\n";
    print $app_fh
      "    This routine initializes values in the \$args_href which are\n";
    print $app_fh "    specific to this application and this invocation.\n";
    print $app_fh "\n";
    print $app_fh
      "    This should be the last init routine called from the MAIN block .\n";
    print $app_fh "\n";
    print $app_fh "    Usage:\n";
    print $app_fh "\n";
    print $app_fh "        \$args_href = init_local_data(\$args_href);\n";
    print $app_fh "\n";
    print $app_fh "=cut\n";
    print $app_fh "\n";
    print $app_fh
"#-------------------------------------------------------------------------------\n";
    print $app_fh "\n";
    print $app_fh "sub init_local_data (\$;) {\n";
    print $app_fh "\n";
    print $app_fh "    my \$sub = ( caller(0) )[3];\n";
    print $app_fh "    trace_enter(\$sub);\n";
    print $app_fh "\n";
    print $app_fh "    my \$args_href = shift;\n";
    print $app_fh "\n";
    print $app_fh "    # some local data\n";
    print $app_fh "    my \$app_name = \"$app_name\";\n";
    print $app_fh "    my \$version  = \"1.0\";\n";
    print $app_fh "\n";
    print $app_fh "    \$args_href->{\'version\'}  = \$version;\n";
    print $app_fh "    \$args_href->{\'app_name\'} = \$app_name;\n";
    print $app_fh "\n";
    print $app_fh "    if ( \$args_href->{\'version_arg\'} ) {\n";
    print $app_fh "\n";
    print $app_fh "        # print version information\n";
    print $app_fh "        my \$msg = \"\n";
    print $app_fh "\n";
    print $app_fh "             \$app_name\n";
    print $app_fh "\n";
    print $app_fh "             Version (\$version)\n";
    print $app_fh "             Copyright $organization $year\n";
    print $app_fh "\n";
    print $app_fh "        \";\n";
    print $app_fh "\n";
    print $app_fh "        print \"\$msg\\n\";\n";
    print $app_fh "\n";
    print $app_fh "        trace_exit(\$sub);\n";
    print $app_fh "        exit 0;\n";
    print $app_fh "    }\n";
    print $app_fh "\n";
    print $app_fh "    trace_exit(\$sub);\n";
    print $app_fh "    return \$args_href;\n";
    print $app_fh "}\n";
    print $app_fh "\n";
    print $app_fh
"#-------------------------------------------------------------------------------\n";
    print $app_fh "\n";

    print $app_fh "=head3 MAIN()\n";
    print $app_fh "\n";
    print $app_fh "    The main entry point to the application.\n";
    print $app_fh "\n";
    print $app_fh
"    This is sthe block where the Developer starts the POP program narrative\n";
    print $app_fh "    for the Reader.\n";
    print $app_fh "\n";
    print $app_fh "    The structure of this application is:  TODO \n";
    print $app_fh "\n";
    print $app_fh "=cut\n";
    print $app_fh "\n";
    print $app_fh
"#-------------------------------------------------------------------------------\n";
    print $app_fh "\n";
    print $app_fh "{    # MAIN main Main block\n";
    print $app_fh "\n";
    print $app_fh
"    my \$sub = \"MAIN\";    # \$sub is a literal string, since MAIN is just a block\n";
    print $app_fh "    trace_enter(\$sub);\n";
    print $app_fh "\n";
    print $app_fh "    my \$args_href;\n";
    print $app_fh "\n";
    print $app_fh "    # initialize the shared data for the application\n";
    print $app_fh "\n";
    print $app_fh
      "    \$args_href = parse_commandline_arguments(\$args_href);\n";
    print $app_fh "    \$args_href = "
      . $app_name
      . "_init_common_data(\$args_href);\n";
    print $app_fh "    \$args_href = init_local_data(\$args_href);\n";
    print $app_fh "\n";
    print $app_fh "    # \n";
    print $app_fh "    # Start of the Narrative for the Reader\n";
    print $app_fh "    # \n";
    print $app_fh "    # TODO\n";
    print $app_fh "    # \n";
    print $app_fh "\n";
    print $app_fh "\n";
    print $app_fh "    trace_exit(\$sub);\n";
    print $app_fh "    exit $true;\n";
    print $app_fh "\n";
    print $app_fh "}\n";
    print $app_fh "\n";
    print $app_fh
"#-------------------------------------------------------------------------------\n";
    print $app_fh "\n";
    print $app_fh "=head1 ^\n";
    print $app_fh "\n";
    print $app_fh "=cut\n";
    print $app_fh "\n";
    print $app_fh "# EOF\n";
    print $app_fh "\n";

    close($app_fh);

    trace_exit($sub);
    return $true;
}

#-----------------------------------------------------------------------------------------------------

=head3 poparazzi_dialog_continue ($;$)

    Desc:       Continue a dialog with the user on the command line

    Parameters : $continue_msg
    Return     : $response

    Usage:

         my $response = poparazzi_dialog_continue ("Please enter another name");

       

=cut

#-----------------------------------------------------------------------------------------------------

sub poparazzi_dialog_continue ($;$) {

    my $sub = ( caller(0) )[3];
    trace_enter($sub);

    my $msg      = shift;
    my $default  = shift;
    my $response = undef;

    while ( !$response ) {

        print "    ==> $msg: ";
        print " [$default]: " if $default;
        chomp( $response = <STDIN> );

        # user enters a response
        if ($response) {
            trace_exit($sub);
            return $response;
        }

        # user selects default with <CR>
        if ( !$response or $response eq "" or $response eq "\n" ) {
            trace_exit($sub);
            return $default;
        }

        # otherwise reprint message
        print "    ==> CTRL-C to exit";
    }

    print "FATAL ERROR $sub: went someplace imposible\n";
    trace_exit($sub);
    exit $false;
}

#-----------------------------------------------------------------------------------------------------

=head3 poparazzi_dialog_end ($;)

    Desc:       End a dialog with the user on the command line

    Parameters :  $end_query_
    Return     :  $true if ending $false if not ending

    Usage:

         my $status = poparazzi_dialog_end ("Are you done entering names")
       

=cut

#-----------------------------------------------------------------------------------------------------

sub poparazzi_dialog_end ($;) {

    my $sub = ( caller(0) )[3];
    trace_enter($sub);

    my $end_query = shift;

    #print "$end_query [y\/n]: ";

    my $response = <>;

    if ( $response eq 'y' ) {

        trace_exit($sub);
        return $true;
    }

    trace_exit($sub);
    return $false;
}

#-----------------------------------------------------------------------------------------------------

=head3 poparazzi_dialog_start ($$;$;)

    Desc:        Start a dialog with the user on the command line

    Parameters : $intro $query, $default
    Return     : $response or $default

    Usage:

        my $response = poparazzi_dialog_start ( "This does this and that.", "Continue?",  "default" );
       

=cut

#-----------------------------------------------------------------------------------------------------

sub poparazzi_dialog_start ($$;$) {

    my $sub = ( caller(0) )[3];
    trace_enter($sub);

    my $intro   = shift;
    my $msg     = shift;
    my $default = shift;

    my $response = undef;

    print "$intro\n";

    while ( !$response ) {

        print "    ==> $msg [$default]: ";
        chomp( $response = <STDIN> );

        # user enters a response
        if ($response) {
            trace_exit($sub);
            return $response;
        }

        # user selects default with <CR>
        if ( !$response ) {
            trace_exit($sub);
            return $default;
        }

        # otherwise reprint message
        print "CTRL-C to exit";
    }

    print "FATAL ERROR $sub: went someplace imposible\n";
    trace_exit($sub);
    exit $false;
}

# -----------------------------------------------------------------------------------------------------

=head3 poparazzi_get_csv_utilization_report_by_type($;)

    Query Ecut webservice for resource utiilization csv file by type

    Parameters  : ecut server ip/hostname, resource name
    Return      : array reference (devices)

    Usage:

       my $csv_file_aref = poparazzi_get_csv_utilization_report_by_type( $server, $resource_type, $site );

=cut 

# -----------------------------------------------------------------------------------------------------

sub poparazzi_get_csv_utilization_report_by_type {

    my $sub = ( caller(0) )[3];
    trace_enter($sub);

    my $server        = shift;
    my $resource_type = shift;
    my $site          = shift;

    # define some reusable variables
    my ($msg);

    my $content_type = "application/xml";

    my $browser = LWP::UserAgent->new();

    my $site_str = "";
    if ($site) {
        $site =~ s/\s+/%20/g;
        $site_str = "?site=$site";
    }

    my $http =
"http://$server/viewer/GetListingCsv.action$site_str&type=$resource_type&stream=true";

    my $response = $browser->get( $http, 'Accept' => "$content_type" );

    if ( !$response->is_success ) {

        # debug
        #ref_dump ( $response );

        $msg = "Can't get -- $response->status_line";
        print "FATAL $sub: $msg\n";
        exit;
    }

    my $content_string = $response->{'_content'};
    my @content_array = split( /\n/, $content_string );

    my $total = @content_array;

    if ( $total == 0 ) {

        $msg = "Empty CSV file returned from ECUT";
        print "WARN $sub: $msg\n";

        trace_exit($sub);
        return $false;
    }

    # make sure it is comma separated, not semicolon separated
    my @cleaned_array;
    foreach my $line (@content_array) {
        $line =~ s/;/,/g;
        push( @cleaned_array, $line );
    }
    @content_array = @cleaned_array;

    trace_exit($sub);
    return \@content_array;
}

#-----------------------------------------------------------------------------------------------------

=head3 poparazzi_get_pop_block_by_tag ($$$$;)

    Desc:        Find a section in a POP pm file using a search string.
                 The search string identifies the beginning of the next
                 block. The start_offset is the current index into the
                 input_ffile_href - ie the start of the pop block.

    Parameters : $input_file_aref, $start_offset, $search_str, $seperator

    Return     :  $block_aref and cursor_index or $false

    Usage:

        my ( $block_aref, $cursor_index )  = 
            poparazzi_get_pop_block_by_tag ( $input_file_aref, $start_offset, $search_str, $seperator );

    Notes:

         The currsor_index is the index into the input file array denoting the last
         line of the block.  This can be used to define the first line of the next
         block.  The seperator is usually #--------  it defines pop blocks

=cut

#-----------------------------------------------------------------------------------------------------

sub poparazzi_get_pop_block_by_tag ( $$$$;) {

    my $sub = ( caller(0) )[3];
    trace_enter($sub);

    my $input_file_aref = shift;
    my $start_offset    = shift;
    my $search_str      = shift;
    my $seperator       = shift;

    my @input_file_array = @$input_file_aref;

    # reusable variables
    my ( $line, $msg, $response, $aref, $href, $str, @array );

    #
    # do the search
    #

    my $i         = $start_offset;
    my @cur_array = ();

    while ( $line = $input_file_array[ $i++ ] ) {
        chomp($line);
        push( @cur_array, $line );
        if ( $line =~ $search_str ) {
            while ( $input_file_array[ $i-- ] !~ $seperator ) {
                $line = pop(@cur_array);
            }
            last;
        }
    }

    my $end_index = $i + 1;

    trace_exit($sub);
    return ( \@cur_array, $end_index );
}

#-----------------------------------------------------------------------------------------------------

=head3 poparazzi_get_pop_subroutine_block ($$;)

    Desc:        Capture a POP subroutine from a file aref

    Parameters : $input_file_aref, $start_offset

    Return     :  $block_aref and cursor_index or $false

    Usage:

        my ( $block_aref, $cursor_index )  = 
            poparazzi_get_pop_subroutine_block ( $input_file_aref, $start_offset, );

    Notes:

         The currsor_index is the index into the input file array denoting the last
         line of the block.  This can be used to define the first line of the next
         block.

=cut

#-----------------------------------------------------------------------------------------------------

sub poparazzi_get_pop_subroutine_block ($$;) {

    my $sub = ( caller(0) )[3];
    trace_enter($sub);

    my $input_file_aref = shift;
    my $start_offset    = shift;

    my @input_file_array = @$input_file_aref;

    # reusable variables
    my ( $line, $msg, $response, $aref, $href, $str, @array );

    #
    # do the search
    #

    my $i          = $start_offset;
    my $search_str = "^}";
    my $seperator  = "^#--------------------";

    my @cur_array = ();

    while ( $line = $input_file_array[ $i++ ] ) {
        chomp($line);
        push( @cur_array, $line );
        if ( $line =~ $search_str ) {
            while ( $input_file_array[ $i++ ] !~ $seperator ) {
                push( @cur_array, $line ) if $line !~ $search_str;
            }
            last;
        }
    }

    my $end_index = $i - 1;

    trace_exit($sub);
    return ( \@cur_array, $end_index );
}

# -----------------------------------------------------------------------------------------------------

=head3 poparazzi_get_property_value_by_resource_name ($$$;)

    Gets a proptery value from Ecut by resource type and property name

    Parameters  : $args_href, $resource_type, $property_name

    Return      : sring of property value

    Usage:

       my $prop_string = poparazzi_get_property_value_by_resource_name ( $args_href, $resource_type, $prop_name );

=cut 

# -----------------------------------------------------------------------------------------------------

sub poparazzi_get_property_value_by_resource_name ($$$;) {

    my $sub = ( caller(0) )[3];
    trace_enter($sub);

    my $args_href     = shift;
    my $resource_type = shift;
    my $prop_name     = shift;

    my $server = $args_href->{'pop_server'};

    my $content_type = "application/xml";
    my $browser      = LWP::UserAgent->new();

    my $http =
"http://$server/webservice/resources/$resource_type/property/$prop_name.xml";

    my $response = $browser->get( $http, 'Accept' => "$content_type" );

    if ( !$response->is_success ) {

        my $msg = "ECUT request for \'$prop_name\' failed.";
        print "WARN $sub: $msg\n";

        # ref_dump ( $response );
        #exit;

        trace_exit($sub);
        return '-';
    }

    # property value string as xml
    my $cont_str = $response->{'_content'};

    if ( !$cont_str or $cont_str eq "" ) {

        my $msg = "Could not get a value for $prop_name from ECUT.";
        print "WARN $sub: $msg\n";

        # ref_dump ( $response );
        trace_exit($sub);
        return '-';
    }

    # trim front
    my @array = split( />/, $cont_str );
    my $ret_str = $array[1];

    # trim end
    @array = split( /</, $ret_str );
    $ret_str = $array[0];

    chomp $ret_str;

    # return value without the xml
    trace_exit($sub);
    return $ret_str;
}

# -----------------------------------------------------------------------------------------------------

=head3 poparazzi_get_resources_by_type($;)

    Query Ecut webservice for resources  by type

    Parameters  : ecut server ip/hostname, resource name
    Return      : array reference (devices)

    Usage:

       my $query_aref = poparazzi_get_resources_by_type( $server, $resource_type, $site );

=cut 

# -----------------------------------------------------------------------------------------------------

sub poparazzi_get_resources_by_type {

    my $sub = ( caller(0) )[3];
    trace_enter($sub);

    my $server        = shift;
    my $resource_type = shift;
    my $site          = shift;

    my $content_type = "application/xml";

    my $browser = LWP::UserAgent->new();

    my $site_str = "";
    if ($site) { $site =~ s/\s+/%20/g; $site_str = "\/site\/$site"; }

    my $http =
        "http://$server"
      . "/webservice/resources/type/$resource_type"
      . $site_str;

    my $response = $browser->get( $http, 'Accept' => "$content_type" );

    # Check the return code before.
    if ( $response->content_type ne $content_type ) {
        my $msg = "Expecting $content_type, found $response->content_type";
        print "FATAL $sub: $msg\n";
        exit;
    }

    if ( !$response->is_success ) {
        my $msg = "Can't get -- $response->status_line";
        print "FATAL $sub: $msg\n";
        exit;
    }

    my $dev = poparazzi_parse_webservice_response( $response, $resource_type );
    my $total = scalar(@$dev);

    if ( $total > 0 ) {
        trace_exit($sub);
        return $dev;
    }

    trace_exit($sub);
    return 0;
}

#-----------------------------------------------------------------------------------------------------

=head3 poparazzi_insert_use_statements_to_module_file ($$;)

    Desc:        Insert 'use' statements to a moduel file

    Parameters : $args_href, $dialog_href
    Return     :  $true or $false

    Usage:

        my $status = 
            poparazzi_insert_use_statements_to_module_file ( $args_href, $dialog_href );


=cut

#-----------------------------------------------------------------------------------------------------

sub poparazzi_insert_use_statements_to_module_file ( $$;) {

    my $sub = ( caller(0) )[3];
    trace_enter($sub);

    my $args_href   = shift;
    my $dialog_href = shift;

    my $mod_filename = $dialog_href->{'mod_filename'};
    my $pkg_list     = $dialog_href->{'pkg_list'};

    my $input_filename  = $mod_filename;
    my $output_filename = "$mod_filename.POP";

    # reusable variables
    my ( $msg, $response, $aref, $href, $str, @array );

    # pkg_list needs to have contents
    if ( !$pkg_list or $pkg_list eq "" ) {
        $msg = "Undefined or empty list of packages...";
        print "FATAL $sub: $msg\n";
        exit 0;
    }
    my @pkg_array = split( " ", $pkg_list );

    if ( !-e $input_filename ) {
        $msg = "$input_filename does not exist.  Exiting...";
        print "FATAL $sub: $msg\n";
        exit 0;
    }

    # see if output file already exists
    if ( -e $output_filename ) {

        $msg = "overwrite $output_filename  (y\/n)?";
        $response = poparazzi_dialog_continue( $msg, 'n' );

        if ( $response eq 'n' ) {
            trace_exit($sub);
            return $true;
        }
    }

    # read the input module file
    $aref = pop_slurp_file_into_aref($input_filename);
    my @input_file_array = @$aref;

    # create the output file handle
    my $output_fh = pop_create_w_filehandle($output_filename);

    #
    #   Start copying the module file to the temporary .POP file
    #
    #   This parsing strategy assumes that the inputfile has been
    #   run through PerlTidy and that the file has been produced by
    #   poparazzi.  The location of POD directives, use stmts and
    #   opening and closing curly braces can be assumed to be where
    #   they are expected to be.  This is the approach any of the
    #   file altering and scnning functionality will be implemented
    #   in the first release of poparazzi.

    my $first_search_tag  = "    use warnings";    # pod  entry
    my $second_search_tag = "^use warnings";       # code entry
    my @local_use_array = @pkg_array;    # init with the pkg list argument
    my $pkg_arg_count   = @pkg_array;

    my $i = 0;
    my $j = $pkg_arg_count;
    my $line;

    #
    # Get the list of code-level 'use' statements
    # as an array from the file, and add the list
    # from the arguments.
    #

    while ( $line = $input_file_array[ $i++ ] ) {
        last if $line =~ $second_search_tag;
    }

    while ( $line = $input_file_array[ $i++ ] ) {

        if ( $line =~ "^use" ) {

            # strip off leading 'use ' and add to array
            my ( $dont_care, $pkg ) = split( " ", $line );
            $local_use_array[ $j++ ] = $pkg;
        }
        last if $line =~ "^=cut";
    }

    # remove duplicate package names and sort array
    my $tmp_href = {};
    foreach my $key (@local_use_array) {
        $tmp_href->{$key} = 0;
    }
    @local_use_array = keys %$tmp_href;
    @local_use_array = sort @local_use_array;

    #
    #  write the POD-level package statements
    #

    $i = 0;    # restart iterator
    while ( $line = $input_file_array[ $i++ ] ) {

        print $output_fh $line;

        if ( $line =~ $first_search_tag ) {

            # print use statements to the POD block
            print $output_fh "\n";
            foreach my $pkg (@local_use_array) {
                if ( $pkg =~ ";" ) {
                    print $output_fh "    use $pkg\n";
                }
                else {
                    print $output_fh "    use $pkg;\n";
                }
            }
            last;
        }
    }

    # skip any other use statements in the POP header
    # since they were just added to the file.
    while ( $line = $input_file_array[ $i++ ] ) {
        if ( $line =~ "^=cut" ) {
            print $output_fh "\n$line";
            last;
        }
    }

    #
    # write the code-level package statements
    #
    while ( $line = $input_file_array[ $i++ ] ) {

        print $output_fh $line;

        if ( $line =~ $second_search_tag ) {

            # print use statements to the POD block
            print $output_fh "\n";
            foreach my $pkg (@local_use_array) {
                if ( $pkg =~ ";" ) {
                    print $output_fh "use $pkg\n";
                }
                else {
                    print $output_fh "use $pkg;\n";
                }
            }
            last;
        }
    }

    # skip any other use statements in the code
    # since they were just added to the file.
    while ( $line = $input_file_array[ $i++ ] ) {
        if ( $line =~ "^#----------" ) {
            print $output_fh "\n$line";
            last;
        }
    }

    # print the rest of the file
    while ( $line = $input_file_array[ $i++ ] ) {
        print $output_fh $line;
    }

    close($output_fh);

    trace_exit($sub);
    return $true;
}

#-----------------------------------------------------------------------------------------------------

=head3 poparazzi_insert_subroutines_to_module_file ($$;)

    Desc:        Insert subroutines stubs to a moduel file

    Parameters : $args_href, $dialog_href

    Return     :  $true or $false

    Usage:

        my $status = 
            poparazzi_insert_subroutines_to_module_file ( $args_href, $dialog_href );


=cut

#-----------------------------------------------------------------------------------------------------

sub poparazzi_insert_subroutines_to_module_file ( $$;) {

    my $sub = ( caller(0) )[3];
    trace_enter($sub);

    my $args_href   = shift;
    my $dialog_href = shift;

    my $app_name     = $dialog_href->{'app_name'};
    my $app_filename = $dialog_href->{'app_filename'};
    my $mod_name     = $dialog_href->{'mod_name'};
    my $mod_filename = $dialog_href->{'mod_filename'};

    my $input_filename = $dialog_href->{'mod_filename'};
    my $sub_list_str   = $dialog_href->{'sub_list_str'};

    my $output_filename = "$mod_filename.POP";

    # reusable variables
    my ( $msg, $response, $print_aref, $aref, $href, $str, @array );

    # sub_list_str needs to have contents
    if ( !$sub_list_str or $sub_list_str eq "" ) {
        $msg = "Undefined or empty list of subroutines...";
        print "FATAL $sub: $msg\n";
    }
    my @new_sub_list_array = split( " ", $sub_list_str );
    foreach my $name (@new_sub_list_array) {
        $name = $app_name . "_" . $name;
    }

    # see if output file already exists
    if ( -e $output_filename ) {

        $msg = "overwrite $output_filename  (y\/n)?";
        $response = poparazzi_dialog_continue( $msg, 'n' );

        if ( $response eq 'n' ) {
            trace_exit($sub);
            return $true;
        }
    }

    # turn the module file contents into a hash of code blocks
    my $file_href =
      poparazzi_decompose_module_file( $args_href, $input_filename );

    #
    # create the output file handle
    #
    my $output_fh = pop_create_w_filehandle($output_filename);

    #
    #  Copy the module file to the temporary .POP file
    #  inserting the new subroutines
    #

    # file header
    $print_aref = $file_href->{'file_header_aref'};
    foreach my $line (@$print_aref) { print $output_fh "$line\n"; }

    # file history
    $print_aref = $file_href->{'file_history_aref'};
    foreach my $line (@$print_aref) { print $output_fh "$line\n"; }

    # pod dependencies section
    $print_aref = $file_href->{'pod_depends_aref'};
    foreach my $line (@$print_aref) { print $output_fh "$line\n"; }

    # code dependencies section
    $print_aref = $file_href->{'code_depends_aref'};
    foreach my $line (@$print_aref) { print $output_fh "$line\n"; }

    # sub_section_header section
    $print_aref = $file_href->{'subs_section_header_aref'};
    foreach my $line (@$print_aref) { print $output_fh "$line\n"; }

    #
    # Working with subroutines here
    #

    # print the init_common_data subs first

    $aref = $file_href->{'subroutine_names_aref'};
    my @sub_names = @$aref;

    # combine new and existing sub names
    push( @sub_names, @new_sub_list_array );

    # separate the init_common_data subroutines into their
    # own array.  Then sort and remove duplications
    my @init_names_array = grep /init_common_data/, @sub_names;
    my %hash = map { $_, 1 } @init_names_array;
    @init_names_array = keys %hash;
    @init_names_array = sort @init_names_array;

    # Remove init subs from the list of sub names
    # then sort and remove duplications
    @sub_names = grep !/init_common_data/, @sub_names;
    %hash      = map { $_, 1 } @sub_names;
    @sub_names = keys %hash;
    @sub_names = sort @sub_names;

    foreach my $sub_name (@init_names_array) {
        my $sub_aref = $file_href->{'subroutines'}->{$sub_name};

        if ($sub_aref) {
            my $code_aref =
              $file_href->{'subroutines'}->{$sub_name}->{'code_block_aref'};

            # print the sub_name code_block
            foreach my $line (@$code_aref) { print $output_fh "$line\n"; }
        }
        else {
            # print a new subroutine template with $sub_name
            poparazzi_write_new_subroutine_block( $output_fh, $app_name,
                $sub_name );
        }
    }
    print $output_fh "\n";

    #
    # print the rest of the sub to the module file
    #
    foreach my $sub_name (@sub_names) {
        my $sub_aref = $file_href->{'subroutines'}->{$sub_name};

        if ($sub_aref) {
            my $code_aref =
              $file_href->{'subroutines'}->{$sub_name}->{'code_block_aref'};

            # print the sub_name code_block
            foreach my $line (@$code_aref) { print $output_fh "$line\n"; }
        }
        else {
            # print a new subroutine template with $sub_name
            poparazzi_write_new_subroutine_block( $output_fh, $app_name,
                $sub_name );
        }
    }

    #print $output_fh "\n";

    # module file footer
    $print_aref = $file_href->{'file_footer_aref'};
    foreach my $line (@$print_aref) { print $output_fh "$line\n"; }

    close($output_fh);

    trace_exit($sub);
    return $true;
}

#-------------------------------------------------------------------------------

=head3 poparazzi_log($$;)

    This routine is a simple interfaces to the logging system.
    Currently this is the syslog system but it wraps whatever may
    be used in the future.

    Usage:

        poparazzi_log ( "LOG_INFO",    $msg );  # informational message - logs and returns
        poparazzi_log ( "LOG_WARN", $msg );  # warning message       - logs and returns
        poparazzi_log ( "LOG_ERR",     $msg );  # error message         - logs and returns
        poparazzi_log ( "LOG_CRIT",    $msg );  # fatal message         - logs and exit 0

=cut

#-------------------------------------------------------------------------------

sub poparazzi_log($$;) {

    my $sub = ( caller(0) )[3];
    trace_enter($sub);

    my $log_type = shift;
    my $msg      = shift;

    if (   ( $log_type ne "LOG_INFO" )
        && ( $log_type ne "LOG_WARN" )
        && ( $log_type ne "LOG_ERR" )
        && ( $log_type ne "LOG_CRIT" ) )
    {
        print
          " WARN  $sub : programming err: log type ($log_type) unsupported\n";
        print
          "        must be one of (LOG_INFO, LOG_WARN, LOG_ERR, LOG_CRIT)\n";
        print
"  eg: poparazzi_log ( \"LOG_INFO\", \"passed in an unsupported type to the $sub\" );\n";
        return $false;
    }

    syslog( $log_type, $msg );

    trace_exit($sub);
    return $true;
}

#-------------------------------------------------------------------------------

=head3 poparazzi_merge_two_hrefs($$;)

  Homegrown href merge.
 
  Usage:

    my $c_href = poparazzi_merge_two_hrefs ( $a_href, $b_href );

=cut

#-------------------------------------------------------------------------------

sub poparazzi_merge_two_hrefs ($$;) {

    my $sub = ( caller(0) )[3];
    trace_enter($sub);

    my $a_href = shift;
    my $b_href = shift;

    my $c_href;

    foreach my $ref ( $a_href, $b_href ) {

        for my $key ( keys %{$ref} ) {
            print "key: $key\n";
            if ( defined $ref->{$key} ) {
                $c_href->{$key} = $ref->{$key};
            }
        }
    }

    return $c_href;
}

# -----------------------------------------------------------------------------------------------------

=head3 poparazzi_parse_webservice_response($$;)

    Convert the Ecut response code into XPath node object

    Parameters  : Ecut responce code
    Return      : array of devices that match by node name, node value.

    Usage: 

        my $ret_aref = poparazzi_parse_webservice_response($pop_response);
        my @array = @$ret_aref;

=cut

# -----------------------------------------------------------------------------------------------------

sub poparazzi_parse_webservice_response($$;) {

    my $sub = ( caller(0) )[3];
    trace_enter($sub);

    #my $pop_parse_webservice_response_start = Benchmark->new;

    my $debug = ( caller(0) )[3] . "(@_)";

    #print LOG "$debug\n" if $::DEBUG;

    my $response = shift;
    my $rtype    = shift;

    my $content = XML::XPath->new( xml => $response->{_content} );
    my @device_list;

    my $href;
    foreach my $node ( $content->find('/resources/resource')->get_nodelist ) {

        my $node_name = $content->find( 'name', $node )->string_value;
        my $node_type = $content->find( 'type', $node )->string_value;
        my $query =
          'properties[@class="linked-hash-map"]/property[@type="String"]';

        my ( $dnsname, $portname );
        foreach my $item ( $content->find( $query, $node )->get_nodelist ) {

            my $name  = $item->find( 'name',  $node )->string_value;
            my $value = $item->find( 'value', $node )->string_value;

            $dnsname  = $value if $name =~ /dnsname/;
            $portname = $value if $name eq "portname";

            # this has to be resource_type for ixia not
            # type_arg or resource_type: ie 'ixia-ports'
            if ( $rtype eq "tgen-ports" ) {

                if ( $dnsname && $portname ) {
                    $href->{DNSNAME}  = $dnsname;
                    $href->{PORTNAME} = $portname;
                    push( @device_list, $href );
                    $href = undef;
                }
            }
            elsif ( $name =~ /dnsname/ ) {

                # just push on the dnsname for other types
                push( @device_list, $dnsname );
                $dnsname = undef;
            }
        }
    }

    # Need to sort and unique the device list
    my $device_list_aref = poparazzi_remove_duplicates( \@device_list );

    trace_exit($sub);
    return ($device_list_aref);
}

# -----------------------------------------------------------------------------------------------------

=head3 poparazzi_ping_device($;)

    Takes device $hostname/ip and pings remote device

    Parameters  : [hostname|fgdn|ip address]
    Return      : returns success/fail 1/0

    Usage: 

        my $status = poparazzi_ping_device( 10.10.10.1 );

=cut

# -----------------------------------------------------------------------------------------------------

sub poparazzi_ping_device($;) {

    my $sub = ( caller(0) )[3];
    trace_enter($sub);

    my $host = shift;

    my $timeout = 3;

    my $p = Net::Ping->new('syn');
    if ( $p->ping( $host, $timeout ) ) {

        my $ack = $p->ack($host);

        if ( $ack and $ack eq $host ) {
            $p->close();
            trace_exit($sub);
            return $true;
        }
    }

    $p = Net::Ping->new('tcp');
    if ( $p->ping( $host, $timeout ) ) {

        my $ack = $p->ack($host);

        if ( $ack and $ack eq $host ) {
            $p->close();
            trace_exit($sub);
            return $true;
        }
    }
    $p->close();

    print " WARN  $sub: ping failed for $host\n";

    trace_exit($sub);
    return $false;
}

# -----------------------------------------------------------------------------------------------------

=head3 deprecated_pop_query_webservice($;)

    Query Ecut webservice for resource by type

    Parameters  : ecut server ip/hostname, resource name
    Return      : array reference (devices)

    Usage:

       my $query_aref = poparazzi_query_webservice( $server, $resource_type, $site );

=cut 

# -----------------------------------------------------------------------------------------------------

sub deprecated_pop_query_webservice {

    my $sub = ( caller(0) )[3];
    trace_enter($sub);

    my $server        = shift;
    my $resource_type = shift;
    my $site          = shift;

    my $content_type = "application/xml";

    my $browser = LWP::UserAgent->new();

    my $http;
    if ($site) {
        $site =~ s/\s+/%20/g;
        $http =
            "http://$server"
          . "/webservice/resources/type/$resource_type"
          . "/site/$site";
    }
    else {
        $http = "http://$server/webservice/resources/type/$resource_type";
    }

    my $response = $browser->get( $http, 'Accept' => "$content_type" );

    # Check the return code before.
    if ( $response->content_type ne $content_type ) {
        my $msg = "Expecting $content_type, found $response->content_type";
        print "FATAL $sub: $msg\n";
        exit;
    }

    if ( !$response->is_success ) {
        my $msg = "Can't get -- $response->status_line";
        print "FATAL $sub: $msg\n";
        exit;
    }

    my $dev = poparazzi_parse_webservice_response( $response, $resource_type );
    my $total = scalar(@$dev);

    if ( $total > 0 ) {
        trace_exit($sub);
        return $dev;
    }
    trace_exit($sub);
    return 0;
}

#-----------------------------------------------------------------------------------------------------

=head3 poparazzi_remove_duplicates($;)

    Returns a unique array preserving the original order; thought that doesn't 
    make total sense, since some elements will be removed.

    Usage:
    
        my $ret_aref = poparazzi_remove_duplicates ( $aref );
=cut

#-----------------------------------------------------------------------------------------------------

sub poparazzi_remove_duplicates ($;) {

    my $sub = ( caller(0) )[3];
    trace_enter($sub);

    my $aref = shift;

    my %seen = ();
    my @r    = ();
    foreach my $a (@$aref) {
        unless ( $seen{$a} ) {
            push @r, $a;
            $seen{$a} = 1;
        }
    }

    trace_exit($sub);
    return \@r;
}

#-------------------------------------------------------------------------------

=head3  poparazzi_slurp_file($;)

    Read ether an 'ini', a 'csv' file or a 'txt' file and return a hash
    reference to the file contents and an array of ordered keys
    
    filename should be the full path to the file

    Usage:

        my ( $href, $aref )  = poparazzi_slurp_file ( "filename.ini" );
        my ( $href, $aref )  = poparazzi_slurp_file ( "filename.csv" );
        my $aref             = poparazzi_slurp_file ( "filename.txt" );

    Notes:

        In the case of a text file, each line in the file 
        is added to an array which is returned as a reference.
        The hash reference is not returned, since a txt file is
        not composed of key value pairs,

=cut

#-------------------------------------------------------------------------------

sub poparazzi_slurp_file ($;) {

    my $sub = ( caller(0) )[3];
    trace_enter($sub);

    my $filename = shift;

    # reusable working variables
    my ( $href, %hash, $aref, $string, $msg );

    if ( !-e $filename ) {

        $msg = "File Not Found: '$filename'";
        print "ERROR $sub : $msg\n";
        trace_exit($sub);
        return $false;
    }

    open( FILE, "<$filename" );    # open for reading
    my @file_contents = <FILE>;    # read into an array
    close(FILE);                   # and close

    my @parts = split( /\./, $filename );
    my $suffix = $parts[$#parts];
    my $sep;                       # the key value seperator

    if ( $suffix eq 'ini' ) {
        $sep = '=';
    }
    if ( $suffix eq 'csv' ) {
        $sep = ',';
    }
    if ( $suffix eq 'txt' ) {
        $sep = "none";
    }

    my ( $ret_href, @ret_array );

    # parse the file into key/value pairs and build
    # the return hash
    foreach my $line (@file_contents) {

        next if !$line;    # line can't be empty
        chomp $line;

        next if $line eq "";       # line can't be blank
        next if $line =~ /^\#/;    # line can't start with a #

        if ( $sep ne 'none' ) {    # line needs a separator if not txt
            next if $line !~ /$sep/;
        }

        my ( $key, $value );

        if ( $suffix eq "txt" ) {    # txt file has a single entry per line

            if ( !$line ) {
                $msg = "malformed line ($line) in $suffix file '$filename'";
                poparazzi_log( "LOG_ERR", $msg );
                print "ERROR $sub : $msg\n";
                trace_exit($sub);
                return $false;
            }

            push( @ret_array, $line );

        }
        else {    # other files have one key and value per line

            ( $key, $value ) = split /$sep/, $line;

            if ( !$key or !$value ) {
                $msg = "malformed line ($line) in $suffix file '$filename'";
                poparazzi_log( "LOG_ERR", $msg );
                print "ERROR $sub : $msg\n";
                trace_exit($sub);
                return $false;
            }

            chomp $key;
            chomp $value;

            push( @ret_array, $key );    # ordered list of keys
            $ret_href->{$key} = $value;  # hash of k/v pairs
        }
    }

    trace_exit($sub);
    return ( $ret_href, \@ret_array );
}

#-----------------------------------------------------------------------------------------------------

=head3 poparazzi_trim($;)

    Trims the leading and tailing whitespace froma string.

    Parameters : $string
    Return     : $string with leading and trailing spaces removed

    Usage:

       $string = poparazzi_trim ( $string );

=cut

#-----------------------------------------------------------------------------------------------------

sub poparazzi_trim($;) {

    my $sub = ( caller(0) )[3];

    #trace_enter($sub);

    my $string = shift;

    $string =~ s/^\s+//;
    $string =~ s/\s+$//;
    $string =~ s/\n{1,}//g;

    #trace_exit($sub);
    return $string;
}

#-----------------------------------------------------------------------------------------------------

=head3 poparazzi_trim_left($;) 

    Leftpop_trim function to remove leading whitespace

=cut

#-----------------------------------------------------------------------------------------------------

sub poparazzi_trim_left($;) {

    my $sub = ( caller(0) )[3];
    trace_enter($sub);

    my $string = shift;
    $string =~ s/^\s+//;

    trace_exit($sub);
    return $string;
}

#-----------------------------------------------------------------------------------------------------

=head3 poparazzi_trim_right($;)

    Rightpop_trim function to remove trailing whitespace

=cut

#-----------------------------------------------------------------------------------------------------

sub poparazzi_trim_right($;) {

    my $sub = ( caller(0) )[3];
    trace_enter($sub);

    my $string = shift;
    $string =~ s/\s+$//;

    trace_exit($sub);
    return $string;
}

#-----------------------------------------------------------------------------------------------------

=head3 poparazzi_update_port_utilization_entry($$$$$$;$) 

    Updates the utilization records using the Ecut webservice

    Parameters :  $args_href, resource type, dnsname, portname_arg, timestamp, state, comment
    Return :      $true on success and $false on failure

    Usage:        my $status = 
                     poparazzi_update_port_utilization_entry
                       ( $args_href, $type, $dnsname, $portname_arg, $timestamp, $state, $comment );

=cut

#-----------------------------------------------------------------------------------------------------

sub poparazzi_update_port_utilization_entry($$$$$$;$) {

    my $sub = ( caller(0) )[3];
    trace_enter($sub);

    my $args_href     = shift;
    my $resource_type = shift;
    my $dnsname_arg   = shift;
    my $portname_arg  = shift;
    my $timestamp     = shift;
    my $state         = shift;
    my $comment       = shift;

    # some devices don't supply a comment
    $comment = "NO COMMENT" if !$comment;

    my $pop_server         = $args_href->{'pop_server'};
    my $pop_server_port    = $args_href->{'pop_server_port'};
    my $pop_auth_user      = $args_href->{'pop_auth_user'};
    my $pop_auth_pw        = $args_href->{'pop_auth_pw'};
    my $aref               = $args_href->{'utilization_states_aref'};
    my @utilization_states = @$aref;
    my $request            = undef;
    my $href_cursor        = undef;

    my $resource_name = "$dnsname_arg-$portname_arg";

    my ( $begin, $end ) = poparazzi_time_get_hour_brackets($timestamp);

    #print "state: $state\n";
    #print "begin: $begin\n";
    #print "end: $end\n";
    #print "resource_name: $resource_name\n";
    #print "comment: $comment\n";

    if ( $begin && $end && $resource_name ) {

        if ( !$state ) {
            print
              "FATAL $sub : the 'state' for $resource_name  is not defined.\n";
            exit $false;
        }
        if ( !grep( $state, @utilization_states ) ) {
            print "FATAL $sub : the state '$state' is not a known state.\n";
            exit $false;
        }

        #
        # construct the xml string to be sent to ECUT for the post
        #

        my $xml = "<utilizations>
           <utilization>
              <state>$state</state>
              <startdate>$begin</startdate>
              <enddate>$end</enddate>
              <resourcename>$resource_name</resourcename>
              <comment>$comment</comment> 
           </utilization>
         </utilizations>";

        my $uar = LWP::UserAgent->new();
        $uar->no_proxy;

        # Ecut queries can be requested by $::SITE_LOCATION
        # but the utilization records do not have site attributes

        #
        # the mechanics of the post
        #
        #print "xml: $xml\n";

        my $server_url =
            'http://'
          . $pop_server . ':'
          . $pop_server_port
          . '/webservice/resources/utilizations';

        $request = new HTTP::Request POST => $server_url;
        $request->content_type('application/xml');
        $request->content("$xml");
        $request->authorization_basic( $pop_auth_user, $pop_auth_pw );

        #
        # here is the response from ECUT
        #

        my $response = $uar->request($request);
        if ( $response->is_error ) {

            my $return_error = $response->error_as_HTML;
            $return_error =~ s/\r\n//g;

            my $msg = "ERROR $sub : $resource_name: $return_error.";
            print "$msg\n";

            # debug
            # ref_dump ( $response );

            #print $response->error_as_HTML . "\n";
            trace_exit($sub);
            return $false;
        }
        else {
            my $success = $response->decoded_content;
            chomp $success;
            $success = poparazzi_trim($success);
            my $msg = "SUCCESS $sub : $resource_name: [$success]";

            #print "$msg\n";

            # debug
            # ref_dump ( $response );

            trace_exit($sub);
            return $true;
        }
    }

    #
    # failed to get the parts of a valid post
    #

    my $rn = "" if !$resource_name;
    my $st = "" if !$begin;
    my $en = "" if !$end;

    my $msg =
      "ERROR $sub : missing resource data: BEGIN=$st END=$en RESOURCE=$rn";
    print "$msg\n";

    trace_exit($sub);
    return $false;
}

#-----------------------------------------------------------------------------------------------------

=head3 poparazzi_post_property_value_by_resource_name($$$$;) 

    Updates a property  record using the Ecut webservice by resource type

    Return :      $true on success and $false on failure

    Usage:        my $status = 
                     poparazzi_post_property_value_by_resource_name
                       ( $args_href, $resource_name, $prop_name, $prop_val );

=cut

#-----------------------------------------------------------------------------------------------------

sub poparazzi_post_property_value_by_resource_name($$$$;) {

    my $sub = ( caller(0) )[3];
    trace_enter($sub);

    my $args_href     = shift;
    my $resource_name = shift;
    my $prop_name     = shift;
    my $prop_val      = shift;

    my $pop_server      = $args_href->{'pop_server'};
    my $pop_server_port = $args_href->{'pop_server_port'};
    my $pop_auth_user   = $args_href->{'pop_auth_user'};
    my $pop_auth_pw     = $args_href->{'pop_auth_pw'};

    my $request     = undef;
    my $href_cursor = undef;

    if ( !$prop_name ) {
        my $msg = "the 'propery_name' for $resource_name  is not defined.";

        # debug
        #print "WARN $sub: $msg\n";

        return $false;
    }
    if ( !$prop_val ) {
        my $msg = "the 'propery_value' for $prop_name is not defined.";

        # debug
        #print "WARN $sub: $msg\n";

        return $false;
    }

    #
    # construct the xml string to be sent to ECUT for the post
    #

    my $xml = "<properties>
           <property>
              <resource_name>$resource_name</resource_name>
              <name>$prop_name</name>
              <value>$prop_val</value>
           </property>
        </properties>";

    my $uar = LWP::UserAgent->new();
    $uar->no_proxy;

    my $server_url =
        'http://'
      . $pop_server . ':'
      . $pop_server_port
      . '/webservice/resources/properties';

    $request = new HTTP::Request POST => $server_url;
    $request->content_type('application/xml');
    $request->content("$xml");
    $request->authorization_basic( $pop_auth_user, $pop_auth_pw );

    #
    # the response from ECUT
    #

    # failure

    my $response = $uar->request($request);

    if ( $response->is_error ) {

        my $return_error = $response->error_as_HTML;
        $return_error =~ s/\r\n//g;

        my $msg = "$resource_name: $return_error.";

        #print "ERROR $sub: $msg\n";

        # debug
        #print $response->error_as_HTML . "\n";

        trace_exit($sub);
        return $false;
    }

    # test the returned value
    my $success = $response->decoded_content;
    chomp $success;

    if ( !$success or $success eq "" ) {

        my $return_error = $response->error_as_HTML;
        $return_error =~ s/\r\n//g;

        my $msg = "$resource_name: $return_error.";

        # debug
        #print "WARN $sub: $msg\n";

        # debug
        #print $response->error_as_HTML . "\n";

        trace_exit($sub);
        return $false;
    }

    # success

    $success = poparazzi_trim($success);
    my $msg = "$resource_name: [$success]/$prop_name/$prop_val";

    # debug
    #print "SUCCESS $sub: $msg\n";

    trace_exit($sub);
    return $true;
}

#----------------------------------------------------------------------------
# tgen Mail Routines

=head2 Mail Handling Routines

    These routines handle mail and messaging between application
    programs and mail recipients.

=head3 poparazzi_mail_create_header($$$;)

    Arguments:
        $args_href
        address
        subject
        Returns: 0 - success
        1 - failure
        Create the header for a sendmail message.

    Usage:

        my $status = poparazzi_mail_create_header ( $args_href, $address, $subject );

=cut

#---------------------------------------
sub poparazzi_mail_create_header($$$;) {

    my $sub = ( caller(0) )[3];
    trace_enter($sub);

    my $args_href     = shift;
    my $address       = shift;
    my $subject       = shift;
    my $resource_type = $args_href->{'resource_type'};

    return $true if !$args_href->{'mailto_arg'};

    my $header;
    $header = "To: $address \n";
    $header .= "From: $resource_type ECUT collector\n";
    $header .= "Subject: $subject \n";
    $header .= "MIME-Version: 1.0 \n";
    $header .= "Content-Type: text/html; charset='iso-8859-1'\n";
    $header .= "Content-Transfer-Encoding: 7bit\n";
    $header .= "<font size='2' face='Verdana'>\n";

    trace_exit($sub);
    return $header;
}

#-------------------------------------------------------------------------------

=head3 poparazzi_mail_create_administrator_email_heading($;) 

    Creates the csv text for a new linecard entry in a status
    email message.

    Usage:

        my $message = poparazzi_mail_create_administrator_email_heading();

=cut

#-------------------------------------------------------------------------------

sub poparazzi_mail_create_administrator_email_heading(;) {

    my $sub = ( caller(0) )[3];
    trace_enter($sub);

    my $message = "Hostname,";
    $message .= "Controller Type,";
    $message .=
"Ports in the ECUT Database that aren't Installed on the Traffic Generator,";
    $message .=
"Ports Installed on the Traffic Generator that Don't Exist in the ECUT Database,";
    $message .= "Linecard Type,";
    $message .= "Linecard Serial Number,";
    $message .= "Number of Ports on Linecard\n";

    trace_exit($sub);
    return $message;
}

#-------------------------------------------------------------------------------

=head3 poparazzi_mail_create_import_administrator_email_heading($;)

    Creates the csv text for a new linecard entry in a status
    email message.

    Usage:

        my $message = poparazzi_mail_create_import_administrator_email_heading();

=cut

#-------------------------------------------------------------------------------

sub poparazzi_mail_create_import_administrator_email_heading(;) {

    my $sub = ( caller(0) )[3];
    trace_enter($sub);

    my $message = "name,";
    $message .= "portname,";
    $message .= "dnsname,";
    $message .= "resource_type,";
    $message .= "site,";
    $message .= "stakeholder\n";

    trace_exit($sub);
    return $message;
}

#-------------------------------------------------------------------------------

=head3 poparazzi_mail_log_to_file_attachment($$;)

    This routine creates a csv mail attachment file.
    Log to status to this file as needed.

    Usage:

        $status = poparazzi_mail_log_to_file_attachment ( $args_href, $message );

=cut

#-------------------------------------------------------------------------------

sub poparazzi_mail_log_to_file_attachment($$;) {

    my $sub = ( caller(0) )[3];
    trace_enter($sub);

    my $args_href = shift;
    my $msg       = shift;

    # open the alert file - used as the mail message body
    my $filename = $args_href->{'mail_attachment_filename'};
    open( MFILE, ">>$filename" ) or die("Failed to open $filename\n");
    print MFILE "$msg" if $msg;    # write msg to file
    close(MFILE);                  # and close

    # might be a better place for this
    system("chmod 777 $filename");

    trace_exit($sub);
    return $true;
}

#-------------------------------------------------------------------------------

=head3 poparazzi_mail_log_to_import_file_attachment($$;)

    This routine creates a csv mail attachment file.
    Log to status to this file as needed.

    Usage:

        $status = poparazzi_mail_log_to_import_file_attachment ( $args_href, $message );

=cut

#-------------------------------------------------------------------------------

sub poparazzi_mail_log_to_import_file_attachment($$;) {

    my $sub = ( caller(0) )[3];
    trace_enter($sub);

    my $args_href = shift;
    my $msg       = shift;

    # open the alert file - used as the mail message body
    my $filename = $args_href->{'mail_import_attachment_filename'};
    open( MFILE, ">>$filename" ) or die("Failed to open $filename\n");
    print MFILE "$msg" if $msg;    # write msg to file
    close(MFILE);                  # and close

    # might be a better place for this
    system("chmod 777 $filename");

    trace_exit($sub);
    return $true;
}

#-------------------------------------------------------------------------------

=head3 poparazzi_mail_log_to_message_body($$;)

    This routine adds an entry to the alert mail file

    Usage:

        $status = poparazzi_mail_log_to_message_body ($args_href, $message );

=cut

#-------------------------------------------------------------------------------

sub poparazzi_mail_log_to_message_body($$;) {

    my $sub = ( caller(0) )[3];
    trace_enter($sub);

    my $args_href = shift;
    my $msg       = shift;

    # open the message file - used as the mail message body
    my $filename = $args_href->{'mail_message_body'};
    open( FILE, ">>$filename" );    # open for appending
    print FILE "$msg";              # write msg to file
    close(FILE);                    # and close

    trace_exit($sub);
    return $true;
}

#---------------------------------------

=head3 poparazzi_mail_message_send($$$$;$$)

    Arguments: $args_href
               $subject
               $address
               $body
               $attachment (optional)
               $import_attachment (optional)

    Returns: 0 - success
              1 - failure
              Send a mail message to an address using
              only the 'body' argument.

=cut

#---------------------------------------
sub poparazzi_mail_message_send($$$$;$$) {

    my $sub = ( caller(0) )[3];
    trace_enter($sub);

    my $args_href         = shift;
    my $subject           = shift;
    my $address_arg       = shift;
    my $body              = shift;
    my $attachment        = shift;
    my $import_attachment = shift;

    return $true if !$address_arg;
    chomp $address_arg;

    if ( !defined $address_arg or $address_arg eq 'none' ) {
        my $msg = " WARN  $sub: no recipient email address provided";

        print "$msg\n";

        trace_exit($sub);
        return $false;
    }

    my $address = $address_arg;
    my $msg;

    # make a temporary file in /tmp to hold the message
    # then pass the file to sendmail...
    my $email_file = "/tmp/email_file.$$";

    my $header = poparazzi_mail_create_header( $args_href, $address, $subject );
    my $message = $header . $body;
    open( MAIL, ">$email_file" );
    print MAIL $message;
    close(MAIL);

    my $sendmail = $args_href->{'tool_sendmail'};
    my $mutt     = $args_href->{'tool_mutt'};
    my $mail     = $args_href->{'tool_mail'};
    my $cmd;

    if ($attachment) {
        $cmd =
"echo \"$body\" | $mutt -a $attachment -a $import_attachment -s \"$subject\" -- $address";
    }
    else {
        $cmd = "$sendmail -t < $email_file";
    }

    my ( $status, $rc ) = poparazzi_shell_local( $args_href, $cmd );

    if ( $status == $false ) {
        $msg = " WARN  $sub: Sendmail command failed";
        poparazzi_log( "LOG_WARN", $msg );

        print "$msg\n";
    }
    else {
        $msg = "INFO $sub: mail successfully sent";
        poparazzi_log( "LOG_INFO", $msg );
        print "$msg\n";
    }

    unlink($email_file) if -e $email_file;
    system("rm -f $email_file") if -e $email_file;

    trace_exit($sub);
    return $true;
}

#---------------------------------------

=head3 poparazzi_mail_send_status ($$$$;)

    Arguments: $args_href
               $message
               $attachment (optional)

    Returns: 0 - success
             1 - failure

    Send a message to the --mailto address

=cut

#---------------------------------------
sub poparazzi_mail_send_status ($$$$;) {

    my $sub = ( caller(0) )[3];
    trace_enter($sub);

    my $args_href    = shift;
    my $pop_stats    = shift;
    my $device_stats = shift;
    my $comm_aref    = shift;

    my $resource_type = $args_href->{'resource_type'};

    my $address    = $args_href->{'mailto_arg'};
    my $subject    = "A message from the - $resource_type ECUT collector";
    my $body       = $args_href->{'mail_message_body'};
    my $attachment = $args_href->{'mail_attachment_filename'};
    my $import_attachment = $args_href->{'mail_import_attachment_filename'};

    my $message;

    if ( -e $attachment ) {    # will only exist if it has content

        # writes summary of the attachment to the $body file
        my $status =
          poparazzi_mail_summarize_pop_posts( $args_href, $pop_stats,
            $device_stats, $comm_aref );
    }

    if ( -e $body ) {

        open( MAIL, "<$body" );    # open for reading
        my @file_contents = <MAIL>;    # read into an array
        close(MAIL);                   # and close

        # should work even if $message arg is undefined
        foreach my $line (@file_contents) {
            $message .= "\n$line";
        }

        my $status =
          poparazzi_mail_message_send( $args_href, $subject, $address,
            $message, $attachment, $import_attachment )
          if $args_href->{'mailto_arg'};    # must have a recipient

        unlink($body);
        unlink($attachment);                #if -e $attachment;
        system("rm -f $body");              #if -e $body;
        system("rm -f $attachment");        #if -e $attachment;
    }
    else {
        print " WARN  $sub : no mail message - nothing to send!\n";
    }

    trace_exit($sub);
    return $true;
}

#-------------------------------------------------------------------------------

=head3 poparazzi_mail_summarize_pop_posts($;)

    This routine takes ecut and controller stats, and summarizes them
    into the mail_message_body file.

    This adds a summary to the body of the email message if there is an attachment

    Usage:

        $status = poparazzi_mail_summarize_pop_posts ( $args_href, $ecut, $dnsname );

=cut

#-------------------------------------------------------------------------------

sub poparazzi_mail_summarize_pop_posts($$$;) {

    my $sub = ( caller(0) )[3];
    trace_enter($sub);

    my $args_href      = shift;
    my $missing_ecut   = shift;
    my $missing_device = shift;
    my $comm_aref      = shift;

    # open the alert file - used as the mail message body
    my $attachment = $args_href->{'mail_attachment_filename'};
    my $body       = $args_href->{'mail_message_body'};

    open( FILE, "<$attachment" );    # open for reading
    my @file_contents = <FILE>;      # read into an array
    close(FILE);                     # and close

    my $num_devices   = 0;
    my $num_pop_ports = 0;

    my $resource_type = $args_href->{'resource_type'};
    my $date          = $args_href->{'timestamp'};

    my $msg;
    $msg = "	Resource type: $resource_type\n" if $resource_type;
    $msg = "	Resource type: UNAVAILABLE\n"    if !$resource_type;

    $msg .= "	Date: $date\n";

    $msg .=
"	Number of Ports in the ECUT Database that are missing from a Controller:    $missing_device\n";
    $msg .=
"	Number of Ports on a Controller that are missing from the ECUT Database:    $missing_ecut\n";
    $msg .= "	Hosts with Colllector or Connection Problems:\n";
    foreach my $dname (@$comm_aref) {
        $msg .= "		$dname\n";
    }

    open( BFILE, ">$body" );    # open for writing
    print BFILE "$msg";         # write to file
    close(BFILE);               # and close

    trace_exit($sub);
    return $true;
}

#-------------------------------------------------------------------------------

=head2 ecut router subroutines

=head3 router_check_bindings($;)

    Takes bindings/upbindings for device and compares it to previous
    collected value. if previous value is <, > or prev 0 new >.

    Returns USED/UNUSED state

  Usage:

    $state = router_check_bindings
               ( $args_href, $stat_bindings, $stat_upbindings, $bindings, $upbindings );

=cut

#-------------------------------------------------------------------------------

sub router_check_bindings {

    my $sub = ( caller(0) )[3];
    trace_enter($sub);

    my $args_href       = shift;
    my $stat_bindings   = shift;
    my $stat_upbindings = shift;
    my $bindings        = shift;
    my $upbindings      = shift;

    my ( $used, $unused );

    if ( $bindings <= 1 ) {

        # UNUSED
        $unused = 1;
    }
    elsif ( $bindings == $stat_bindings ) {

        # UNUSED
        $unused = 1;
    }
    elsif ( $bindings > $stat_bindings || $bindings < $stat_bindings ) {

        # USED
        $used = 1;
    }

    if ( $upbindings <= 1 ) {

        # UNUSED
        $unused = 1;
    }
    elsif ( $upbindings == $stat_upbindings ) {

        # UNUSED
        $unused = 1;
    }
    elsif ( $upbindings > $stat_upbindings || $upbindings < $stat_upbindings ) {

        # USED
        $used = 1;
    }

    if ($used)   { $used   = "USED"; }
    if ($unused) { $unused = "UNUSED"; }

    if ($used) {
        return 1, $used;
    }
    elsif ($unused) {
        return 0, $unused;
    }
    else {
        return 0;
    }
}

#-------------------------------------------------------------------------------

=head3 router_check_subscribers($$$;)

    closes a telent connection.

    router_check_subscribers( $args_href, $stat_subscribers, $subscribers );

=cut

#-------------------------------------------------------------------------------

sub router_check_subscribers {

    my $sub = ( caller(0) )[3];
    trace_enter($sub);

    my $args_href        = shift;
    my $stat_subscribers = shift;
    my $subscribers      = shift;

    my ( $used, $unused );

    if ( $subscribers == 0 ) {

        # UNUSED
        $unused = 1;
    }
    elsif ($subscribers > $stat_subscribers
        || $subscribers < $stat_subscribers )
    {
        # USED
        $used = 1;
    }
    elsif ( $subscribers == $stat_subscribers ) {

        # UNUSED
        $unused = 1;
    }

    if ($used)   { $used   = "USED"; }
    if ($unused) { $unused = "UNUSED"; }

    if ($used) {
        return 1;
    }
    elsif ($unused) {
        return 0, $unused;
    }
    else {
        return 0;
    }
}

#-------------------------------------------------------------------------------

=head3 router_check_device_uptime($$$$;)

    Checks a router's uptime and returns stats

  Usage:

    my ( $status, $state ) =
        router_check_device_uptime( $args_href, $timestamp, $uptime, $offset);

  Returns:
    
      status, and eithe 'USED', 'UNUSED' or 'ERROR' as strings.

=cut

#-------------------------------------------------------------------------------

sub router_check_device_uptime {

    my $sub = ( caller(0) )[3];
    trace_enter($sub);

    my $args_href = shift;
    my $timestamp = shift;
    my $uptime    = shift;
    my $T0_offset = shift;

    # we remove timezone from router clock to sync wqith _begin and _end
    # else we could add timezone to_begin _end
    my @time = split( / /, $timestamp );
    $timestamp = $time[0] . " " . $time[1];

    my ( $begin, $end ) = &Get_The_Hour($timestamp);

 #print LOG "INFO $sub: FStart_time=$begin now_time=$timestamp end_time=$end\n";
    my $T0       = poparazzi_convert_to_second($begin);
    my $T0_trail = $T0 - $T0_offset;
    my $T1       = poparazzi_convert_to_second($timestamp);
    my $T2       = poparazzi_convert_to_second($end);

#print LOG "INFO $sub: offsetSEC($T0_offset)=$T0_trail beginSEC=$T0 nowSEC=$T1 endSEC=$T2\n";
    my $TrailSTR = &Convert_To_String($T0_trail);
    my $T0str    = &Convert_To_String($T0);
    my $T1str    = &Convert_To_String($T1);
    my $T2str    = &Convert_To_String($T2);

#print LOG "INFO $sub: TrailSTR=$TrailSTR BeginSTR=$T0str nowSTR=$T1str endSTR=$T2str\n";

    my $T1_trail = $T1 - $T0_trail;
    print LOG "INFO $sub: TOTAL_TRAIL_SECONDS=$T1_trail\n";

    $uptime =~ s/Router Uptime: //;

    #print LOG "INFO $sub: $uptime\n" if ($::DEBUG);

    my @rup = split( / /, $uptime );
    push( @rup, "end", 0 );
    my $seconds = 0;

    foreach (@rup) {
        my $amount = $rup[0];
        my $label  = $rup[1];
        shift(@rup);
        shift(@rup);

        #print LOG "INFO $sub: label=$label value=$amount\n";

        # test for days, hours, minutes, seconds
        # day=86400
        # hour=3600
        # min=60
        # sec=1

        if ( $label =~ /day/ ) {
            $seconds = $seconds + ( 86400 * $amount );

            #print LOG "INFO $sub: $amount days=$seconds\n";
        }
        elsif ( $label =~ /hour/ ) {
            $seconds = $seconds + ( 3600 * $amount );

            #print LOG "INFO $sub: $amount hours=$seconds\n";
        }
        elsif ( $label =~ /minute/ ) {
            $seconds = $seconds + ( 60 * $amount );

            #print LOG "INFO $sub: $amount mins=$seconds\n";
        }
        elsif ( $label =~ /sec/ ) {
            $seconds = $seconds + $amount;

            #print LOG "INFO $sub: $amount secs=$seconds\n";
        }
    }
    print LOG "INFO $sub: ROUTER_UPTIME(Seconds)=$seconds\n";

    if ( $seconds < $T1_trail ) {
        return 1, "USED";
    }
    elsif ( $seconds >= $T1_trail ) {
        return 1, "UNUSED";
    }
    else {
        return 0, "ERROR";
    }
}

#-------------------------------------------------------------------------------

=head3 router_determine_utiilization_state($$$;)

    Creates the device_href data structure, which is used
    for posting and auditing.

  Usage:

    $device_href = router_determine_utiilization_state( $args_href, $dnsname, $exp );

  Notes:

    The approach here is to go through a list of 6 crieria and contunue
    until a devices is determined to be used or all tests have failed
    in which case the device is unused.

=cut

#-------------------------------------------------------------------------------

sub router_determine_utiilization_state($$$;) {

    my $sub = ( caller(0) )[3];
    trace_enter($sub);

    my $args_href = shift;
    my $dnsname   = shift;
    my $exp       = shift;

    my $mgmt_binding = $args_href->{'mgmt_binding'};
    my $stats_fh     = $args_href->{'stats_file_handle'};
    my $timestamp    = $args_href->{'timestamp'};

    my ( $device_href, $msg );

    # First check/get the bindings.
    # If > 1, run the IO collection test

    $msg = "Collecting stats for $dnsname ...";
    print " INFO $sub: $msg\n";
    print LOG "$msg\n";

    # TODO: Could add a statistics file checking
    # subroutine here to ensure the stats file has
    # no errors

    # my $checkstats = &Check_Statistics_History();
    my $checkstats = 1;

    if ( !$checkstats ) {
        $msg = " $sub(error) : ";
        $msg .= "Check_Statistics_History returned errors";
        print LOG "$msg\n";
    }

    # get the current device bindings
    my ( $got_bindings_bool, $bindings, $up_bindings ) =
      router_get_device_bindings( $args_href, $dnsname, $exp );

    $device_href->{$dnsname}->{'got_bindings'} = $got_bindings_bool;
    $device_href->{$dnsname}->{'bindings'}     = $bindings;
    $device_href->{$dnsname}->{'up_bindings'}  = $got_bindings_bool;

    my ( $io_test, $io_status, @timestamps );

    #
    # Run the IO tests checking for up to the minute
    # packet/sent/recv rates or comparing hourly
    # packet/sent/recv totals
    #

    if ( $up_bindings > $mgmt_binding ) {

        # run the IO test
        print LOG " main : DEVICE( bindings > 1 ) = $dnsname $_ \n ";
        print LOG " main : TIMESTAMP = $timestamp \n ";

        # if REMOTE_CLOCK is enabled pass in the router_clock here
        ( $io_test, $io_status ) =
          router_collect_io_stats( $args_href, $stats_fh,
            $dnsname, $timestamp, $exp, \@timestamps );

        my $pass_fail = "IOTEST_PASSED" if $io_test == 1 || $io_test == 0;
        $pass_fail = "IOTEST_FAILED";
        print LOG " INFO $sub: $pass_fail status = $io_status \n \n ";

        print LOG " INFO $sub: IOTEST_FAILED status = $io_status \n \n ";

        $device_href->{$dnsname}->{'io_test'}   = $io_test;
        $device_href->{$dnsname}->{'io_status'} = $io_status;

    }
    elsif ( $up_bindings == $mgmt_binding ) {

        # device UNUSED

        $msg = "Only one binding found for $dnsname ...";
        print " INFO $sub: $msg\n";
        print LOG "$msg\n";

        $device_href->{$dnsname}->{'pop_status'} = 'UNUSED';
    }
    else {

        # device UNUSED

        $msg = "UPBINDINGS = $up_bindings MGMT_BINDING = $mgmt_binding";
        print "INFO $sub: $msg\n";

        $msg = "0 up bindings on $dnsname ... \n ";
        print " ERROR $sub: $msg\n";
        print LOG "ERROR $sub: $msg\n";

        $device_href->{$dnsname}->{'pop_state'} = 'UNUSED';
    }

    $device_href->{$dnsname}->{'pop_state'} = $io_status;

    # purge the stats file of old entries here
    # devices with same ports as current active
    # are updated by collect_io regardless of timestamp
    # devices with different ports then current active
    # ports (collect_io affects those) and older timestamps
    # are purged

    my $T0_lasttime;

    ( $checkstats, $T0_lasttime ) =
      router_purge_device_stats_history( $args_href, $stats_fh, $dnsname,
        $timestamp, \@timestamps, 1 );

    # TODO: modify purge so it finds last timestamp first, and then
    # purgets the results; not removing entries with last timestamp

    # Debug: force cli testing...
    # undef $io_test;

    #  run the cli test against criteria_1 set of commands
    # if executed within last hour block

    if (  !$io_test
        || $io_status eq " UNUSED "
        || $io_status eq " ERROR " )
    {

        # continue... run the CLI/bindings/subscribers/rup tests

        my $aref = router_get_device_history( $args_href, $dnsname, $exp );
        my @history_array = @$aref;

        #print " >> @history_array << ";

        my (
            $comment,     $rup,          $cli_test_bool,
            $cli_status,  $router_stamp, $router_date,
            $router_time, $router_tz,    $T0_offset
        );
        if (@history_array) {

            $device_href->{$dnsname}->{'history_aref'} = \@history_array;

            # Get router clock, it may be (always is!) skewed
            # from the real remote time and different timezone
            # from script timezone.

            ( $router_stamp, $router_date, $router_time, $router_tz ) =
              router_get_device_time_and_date( $args_href, $dnsname, $exp );

            unless ($router_stamp) {
                $msg = " ERROR $sub: ROUTER_TIMESTAMP = ($router_stamp) ";
                $msg .= "(Could not get remote router clock . ";
                $msg .= "Using server clock for base time)";
                print LOG "$msg\n";
                $router_stamp = $timestamp;
            }
            else {
                $msg = " INFO $sub: ROUTER_TIMESTAMP = $router_stamp";
                $msg .= "router_date = ROUTER_TIMESTAMP = ";
                $msg .= "$router_stamp router_date = $router_date";
                $msg .= " router_time = $router_time router_tz = $router_tz ";
                print LOG "$msg\n";
            }

            #
            # The remote device clocks are always skewed!
            # so we use the remote clock to parse the remote hourly
            # logs. If remote_clock is enabled we use remote TZ
            # to update ecut else we use local script time.
            #
            # trail_offset = (take nowtime - lasttimestamp) in
            # seconds.  This is the time since last script run
            # in stats file in seconds.
            #
            my $Tnow = poparazzi_convert_to_second($timestamp);

            # check if the last_timestamp is valid
            if ( $T0_lasttime > 0 ) {
                $T0_offset = $Tnow - $T0_lasttime;
            }
            else {
                $T0_offset = 0;
            }

            $msg = " INFO $sub: ROUTER_CLOCK = $router_stamp ";
            $msg .= "TIMESTAMP = $timestamp ($Tnow) ";
            $msg .= "TO_OFFSET = $T0_offset";
            print LOG "$msg\n";

            my $hourly_history_aref =
              router_parse_history_by_hour( $args_href, $router_stamp,
                $T0_offset, \@history_array );

            $device_href->{$dnsname}->{'hourly_history_aref'} =
              $hourly_history_aref;

            # criteria are read from an '.ini' file in  ecut etc directory
            my $criteria_1 = $args_href->{'criteria_1'};
            ( $cli_test_bool, $cli_status ) =
              router_get_state_from_cli_history( $args_href,
                $hourly_history_aref, $criteria_1 );

            $msg = " main : CLI MESSAGE : $cli_status";
            print LOG "$msg\n";

            if ( $cli_test_bool && $cli_status eq " USED " ) {

                my $device_status = 1;

                # device USED
                $comment = " USED-CLI_activity ";

                $device_href->{$dnsname}->{'pop_state'}     = 'USED';
                $device_href->{$dnsname}->{'device_status'} = $device_status;
                $device_href->{$dnsname}->{'comment'}       = $comment;
            }
        }

        # get the previous bindings and subscribers
        my (
            $getstat,          $stat_bindings, $stat_up_bindings,
            $stat_subscribers, $stat_timestamp
          )
          = router_get_device_stats_history( $args_href, $stats_fh, $dnsname,
            1 );

        $device_href->{$dnsname}->{'stat_bindings'}    = $stat_bindings;
        $device_href->{$dnsname}->{'stat_up_bindings'} = $stat_up_bindings;
        $device_href->{$dnsname}->{'stat_subscribers'} = $stat_subscribers;
        $device_href->{$dnsname}->{'stat_timestamp'}   = $stat_timestamp;

        $msg =
          " stat_bindings = $stat_bindings stat_upbinding = $stat_up_bindings";
        print LOG "$msg\n";

        $msg = " bindings = $bindings up_bindings = $up_bindings";
        print LOG "$msg\n";

        $msg =
" stat_subscribers = $stat_subscribers stat_timestamp = $stat_timestamp";
        print LOG "$msg\n";

        $device_href->{$dnsname}->{'stat_subscribers'} = $stat_subscribers;
        $device_href->{$dnsname}->{'stat_timestamp'}   = $stat_timestamp;

        my ( $got_subscribers_bool, $subscribers ) =
          router_get_subscribers( $args_href, $dnsname, $exp );

        $device_href->{$dnsname}->{'subscribers'} = $subscribers;

        if ( $got_bindings_bool && $got_subscribers_bool ) {
            router_update_device_stats_history(
                $args_href,   $stats_fh,    $dnsname, $bindings,
                $up_bindings, $subscribers, $timestamp
            );

            # Last two conditions are for error catching.
            # IO collect passed but binding or subscriptions
            # has failed
        }
        elsif ($got_bindings_bool) {
            $subscribers = -1;
            router_update_device_stats_history(
                $stats_fh,    $dnsname,     $bindings,
                $up_bindings, $subscribers, $timestamp
            );
        }
        elsif ($got_subscribers_bool) {
            $bindings    = -1;
            $up_bindings = -1;
            router_update_device_stats_history(
                $stats_fh,    $dnsname,     $bindings,
                $up_bindings, $subscribers, $timestamp
            );
        }

        my (
            $bind_test_bool,        $bind_status,
            $subscribers_test_bool, $subscribers_status
        );
        if ( $cli_status eq " UNUSED " || !$cli_test_bool ) {

            # *** prev/current bindings may be null

            unless ($stat_bindings) { $stat_bindings = 0; }
            unless ($stat_up_bindings) {
                $stat_up_bindings = 0;
            }
            unless ($bindings)    { $bindings    = 0; }
            unless ($up_bindings) { $up_bindings = 0; }

            ( $bind_test_bool, $bind_status ) =
              router_check_bindings( $args_href,
                $stat_bindings, $stat_up_bindings, $bindings, $up_bindings );
            $msg = " BINDINGTEST = $bind_test_bool ";
            $msg .= "BINDSTATUS = $bind_status";
            print LOG "$msg\n";

            $device_href->{$dnsname}->{'bind_status'} = $bind_status;

            if ($bind_test_bool) {

                # device USED
                my $device_status = 1;
                $comment = " USED-Bindings_changed ";

                $device_href->{$dnsname}->{'pop_state'} = 'USED';
                $device_href->{$dnsname}->{'comment'}   = $comment;
            }
            else {

                # *** prev/current subscribers may be null
                unless ($stat_subscribers) {
                    $stat_subscribers = 0;
                }
                unless ($subscribers) { $subscribers = 0; }

                ( $subscribers_test_bool, $subscribers_status ) =
                  router_check_subscribers( $args_href,
                    $stat_subscribers, $subscribers );

                $msg = " SUBSCRIPTION = $subscribers_test_bool ";
                $msg .= "SUBSSTATUS = $subscribers_status";
                print LOG "$msg\n";

                if ($subscribers_test_bool) {

                    # device USED;
                    my $device_status = 1;
                    $comment = " USED-Subscribers_changed ";

                    $device_href->{$dnsname}->{'pop_state'} = 'USED';
                    $device_href->{$dnsname}->{'device_status'} =
                      $device_status;
                    $device_href->{$dnsname}->{'comment'} = $comment;
                }
            }
        }

        # Run the router uptime check if it was rebooted
        # within the current hour block
        #
        if ( !$cli_test_bool && !$bind_test_bool && !$subscribers_test_bool ) {

            my ( $rup_test, $rup_message ) =
              router_check_device_uptime( $args_href, $router_stamp, $rup,
                $T0_offset );

            $msg = " INFO $sub : Router_Test = $rup_test STATUS = $rup_message";
            print LOG "$msg\n";

            # Update ecut with final status. this is the
            # only way a device can be UNUSED in ecut.
            #
            if ( $rup_test && $rup_message eq " USED " ) {

                # device USED;
                my $device_status = 1;
                $comment = 'USED-Rebooted';

                $device_href->{$dnsname}->{'pop_state'}     = 'USED';
                $device_href->{$dnsname}->{'device_status'} = $device_status;
                $device_href->{$dnsname}->{'comment'}       = $comment;
            }
            elsif (
                   $rup_test
                && $rup_message eq " UNUSED
              "
              )
            {
                my $device_status = 0;
                $comment = 'UNUSED';

                $device_href->{$dnsname}->{'pop_state'}     = 'UNUSED';
                $device_href->{$dnsname}->{'device_status'} = $device_status;
                $device_href->{$dnsname}->{'comment'}       = $comment;

            }
            elsif ( !$rup_test ) {

                # device ERROR/(ecut status)UNKNOWN;
                my $device_status = 8;
                $comment = 'UNUSED-Rebooted';

                $device_href->{$dnsname}->{'pop_state'}     = 'UNUSED';
                $device_href->{$dnsname}->{'device_status'} = $device_status;
                $device_href->{$dnsname}->{'comment'}       = $comment;
            }
        }
    }
    else {

        # Just update the bindings and subscribers
        my ( $got_subscribers_bool, $subscribers ) =
          router_get_subscribers( $args_href, $dnsname, $exp );

        if ( $got_bindings_bool && $got_subscribers_bool ) {
            &Update_Device_Statistics_History(
                $stats_fh,    $dnsname,     $bindings,
                $up_bindings, $subscribers, $timestamp
            );

        }
        elsif ($got_bindings_bool) {

            #
            # The last two conditions are for error checking.
            # Error condition is: io collect passed but binding
            # or subscriptions has failed
            #
            $subscribers = -1;
            &Update_Device_Statistics_History(
                $stats_fh,    $dnsname,     $bindings,
                $up_bindings, $subscribers, $timestamp
            );
        }
        elsif ($got_subscribers_bool) {
            $bindings    = -1;
            $up_bindings = -1;
            &Update_Device_Statistics_History(
                $stats_fh,    $dnsname,     $bindings,
                $up_bindings, $subscribers, $timestamp
            );
        }
    }
    return $device_href;
}

#-------------------------------------------------------------------------------

=head3 router_get_device_list($$$;) 

    Gets a list of router hostnames to process from the ECUT database based
    on the site and the resource type.

    Usage:

        my $dnsname_aref =
           router_get_device_list( $pop_server, $resource_type, $site );

=cut

#-------------------------------------------------------------------------------

sub router_get_device_list($$$;) {

    my $sub = ( caller(0) )[3];
    trace_enter($sub);

    my $server        = shift;
    my $resource_type = shift;
    my $site          = shift;

    # reusable and return variables
    my ( $aref, $dnsname_aref, $href, $name_port_href );

    my $query_aref = ECUT_Query(
        IP_ADDRESS => $server,
        RESOURCE   => $resource_type,
        SITE       => $site
    );

    if ( !$query_aref or @$query_aref == 0 ) {
        print
          "FATAL $sub: no '$resource_type' devices returned from ($server)\n";
        trace_exit($sub);

        #return $false;
        exit;
    }

    # return an array of unique dnsnames and array of hashes of resources
    trace_exit($sub);
    return ($query_aref);
}

#-------------------------------------------------------------------------------

=head3 router_get_state_from_cli_history ($$$;)

    Takes device history and criteria as csv string
    and searches history logs for commands in criteria.

  Returns:

    Returns status and a 'USED' or  'UNUSED' string

  Usage:

    my ( $status, $state ) = router_get_state_from_cli_history
                   ( $args_href, $history_aref, $criteria );

=cut

#-------------------------------------------------------------------------------

sub router_get_state_from_cli_history($$$;) {

    my $sub = ( caller(0) )[3];
    trace_enter($sub);

    my $args_href      = shift;
    my $hourly_history = shift;
    my $criteria       = shift;

    no strict;
    unless (@$hourly_history) {
        print LOG "INFO $sub: (no hourly history) STATUS=UNUSED\n";

        # no hourly history found
        return 0, "UNUSED";
    }
    use strict;

    my @criteria = split( /,/, $criteria );

    print "Check_CLI_Activity(@_)\n";
    foreach my $c (@$hourly_history) {

        foreach (@criteria) {

            if ( $c =~ /^$_/ || $c =~ /^(.*):$_/ ) {
                print LOG "INFO $sub: criteria_match=($c) STATUS=USED\n";
                print LOG "INFO $sub: STATUS=USED\n";

                return 1, "USED";
            }
        }
    }
    print LOG "INFO $sub: (criteria matched none) STATUS=UNUSED\n";

    # no criteria matched
    return 0, "UNUSED";
}

#-------------------------------------------------------------------------------

=head3 router_parse_history_by_hour($$$$;)

    Takes history and router timestamp extracts history within
    hour bracket of timestamp and returns aref of history commands
    within the hourly bracket 

    my $aref = router_parse_history_by_hour
                 ( $args_href, $timestamp, $offset, $history_aref );

=cut

#-------------------------------------------------------------------------------

sub router_parse_history_by_hour($$$$;) {

    my $sub = ( caller(0) )[3];
    trace_enter($sub);

    my $args_href    = shift;
    my $timestamp    = shift;
    my $T0_offset    = shift;
    my $history_aref = shift;

    my $tztable = $args_href->{'timezone_table'};
    my @hourly_history;

    print LOG "TIMESTAMP=$timestamp\n";
    my @ts   = split( / /, $timestamp );
    my $date = $ts[0];
    my $time = $ts[1];
    my $tz   = $ts[2];
    my @ds   = split( /-/, $date );
    my $year = $ds[0];

    # catch known non-standard remote TZ values that
    # strptime cant handle in Get_The_Hour non standatd
    # timezone abbreviations will break things,
    # re-assign to server timezone

    if ( $tz eq "pacific" ) {
        $tz        = $args_href->{'runtime_tz'};
        $timestamp = $date . " " . $time . " " . $tz;
        print LOG "date=$date time=$time tz_converted=$tz YEAR=$year\n";
    }

    my $Rt = poparazzi_convert_to_second($timestamp);

    # get current the hour block
    # Get_The_Hour has no timezone conversion for its results FIX it
    my ( $begin, $end ) = &Get_The_Hour_TZ($timestamp);
    print LOG "BEGIN=$begin END=$end\n";

    # convert to seconds for begin/end to T1/T2
    my $T1 = poparazzi_convert_to_second($begin);
    my $T2 = poparazzi_convert_to_second($end);

    # Each script may not start/finish same time each hour leaving a
    # gap between end of last and start of current run if we use
    # the entire hour block of the previous hour we always overlap
    # and may detect previous session commands.  To accurately do
    # this we subtract trail_offset from the begin time of the router
    # clock hour block.
    my $T0 = $T1 - $T0_offset;

    print LOG
"\n(remote timezone: $tz)\nT0(offset=$T0_offset)=$T0\nT1=$T1\nRt=$Rt\nT2=$T2\n\n";

    # parse the history between start to end of the current hour
    if ( $Rt >= $T1 && $Rt <= $T2 )
    {    # this requires get_the_hour accept and return timezone in string
        for ( my $i = 0 ; $i < @$history_aref ; $i++ ) {
            if ( $history_aref->[$i] =~
                /^(\w{3})\s(\d+)\s(\d{2}:\d{2}:\d{2})\s((\w|\d|\s)+)$/ )
            {
                print "MATCH(1)=$history_aref->[$i]\n";

                # convert the command line timestamp to seconds
                my $cm = &Month_To_Numeric_Digit($1);
                my $cd = $2;
                my $ct = $3;
                my $cl = $4;
                my $ctimestamp =
                  $year . "-" . $cm . "-" . $cd . " " . $ct . " " . $tz;
                print "COMMAND_TIMESTAMP=$ctimestamp\n";

                my $C1 = poparazzi_convert_to_second($ctimestamp);
                print "C1=$C1\n";

                # compare command line timestamp to the time contraints
                if ( ( $C1 > $T1 ) && ( $C1 < $T2 ) ) {
                    print "PUSH: $history_aref->[$i]\n";

                    #print "CL=$cl\n";
                    push( @hourly_history, $cl );
                }
                else {
                    next;
                }
            }
            elsif ( $history_aref->[$i] =~
                /^(\w{3})\s(\d+)\s(\d{2}:\d{2}:\d{2})\s(.*):((\w|\d|\s)+)/ )
            {
                print "MATCH(2)=$history_aref->[$i]\n";

                # convert the command line timestamp to seconds
                my $cm = &Month_To_Numeric_Digit($1);
                my $cd = $2;
                my $ct = $3;
                my $ad = $4;
                my $cl = $5;
                my $ctimestamp =
                  $year . "-" . $cm . "-" . $cd . " " . $ct . " " . $tz;
                print "COMMAND_TIMESTAMP=$ctimestamp\n";
                my $C1 = poparazzi_convert_to_second($ctimestamp);
                print "C1=$C1\n";

                # compare command line timestamp to the time contraints
                if ( ( $C1 > $T1 ) && ( $C1 < $T2 ) ) {
                    print "PUSH: $history_aref->[$i]\n";

                    #print "CL=$cl\n";
                    push( @hourly_history, $cl );
                }
                else {
                    next;
                }
            }
            else {
                next;
            }
        }
    }
    else {
        return 0;
    }
    return \@hourly_history;
}

#-------------------------------------------------------------------------------

=head3 router_purge_device_stats_history($$$$$$;)

    Purges device statistics history

  Usage:

    router_purge_device_stats_history
        ( $args_href, $fh, $dnsname, $timestamp, $timestamps, $mode ); 

=cut

#-------------------------------------------------------------------------------

sub router_purge_device_stats_history ($$$$$$;) {

    my $sub = ( caller(0) )[3];
    trace_enter($sub);

    my $args_href  = shift;
    my $fh         = shift;
    my $dnsname    = shift;
    my $timestamp  = shift;
    my $timestamps = shift;
    my $mode       = shift;

    my $stats_file = $args_href->{'stats_file'};

    my @statistics;

    if ( -f $stats_file ) {

        print LOG "reading file...\n";

        open( $fh, "<", $stats_file )
          or die "error: Cannot open $stats_file: $!";
        unless ( flock( $fh, LOCK_SH ) ) {
            warn
"$sub: (1) can't immediately read-lock the file ($!), blocking ...";
        }

        my $T1 = poparazzi_convert_to_second($timestamp);

        # parse the timestamps for device
        my $pos = tell($fh);
        while (<$fh>) {
            if ( $_ =~ /^$dnsname\s+/ ) {
                chomp($_);

                #print LOG "MATCH\n";
                #print LOG "line=$_\n";
                my @stat = split( / /, $_ );

                # previous bindings
                my $port        = $stat[1];
                my $psent       = $stat[2];
                my $precv       = $stat[3];
                my $ptimestamp  = $stat[4] . " " . $stat[5] . " " . $stat[6];
                my $bindings    = $stat[7];
                my $upbindings  = $stat[8];
                my $subscribers = $stat[9];
                my $lasttime    = $stat[10] . " " . $stat[11] . " " . $stat[12];
                chomp($lasttime);
                my $stat =
                    $dnsname . " "
                  . $port . " "
                  . $psent . " "
                  . $precv . " "
                  . $ptimestamp . " "
                  . $bindings . " "
                  . $upbindings . " "
                  . $subscribers . " "
                  . $lasttime;

      # time conversions, account for stub port data and select better timestamp
                print LOG "found: STAT($mode): $stat\n";
                if ( $mode == 1 && $port ne "-1/-1" ) {
                    my $T0 = poparazzi_convert_to_second($ptimestamp);
                    push( @$timestamps, $T0 );
                }
                elsif ( $mode == 2 || $port eq "-1/-1" ) {
                    my $T0 = poparazzi_convert_to_second($lasttime);
                    push( @$timestamps, $T0 );
                }
            }
        }

        # get the last timestamp
        my $last = 0;
        my $last_timestamp;
        if (@$timestamps) {
            foreach (@$timestamps) {
                print LOG "timestamps=$_\n";
                if ( $_ > $last && $_ < $T1 ) {
                    $last = $_;
                }
            }

  # catch error in timestamps if any set to current timestamp, uses server clock
            if ( $last > 0 ) {
                $last_timestamp = &Convert_To_String($last);
            }
            else {
                $last_timestamp =
"(purge)LAST_TIMESTAMP=($last) no valid last timestamps, most recent timestamp set to current";
                $last           = $T1;
                $last_timestamp = &Convert_To_String($last);
            }
            print LOG
"(purge)LAST_TIMESTAMP=($last) ($last_timestamp) TIMESTAMP_LOCAL=($T1) ($timestamp)\n";
        }
        else {
            print LOG
              "(purge)LAST_TIMESTAMP=($last) (no recent timestamps in stats)\n";
            $last           = $T1;
            $last_timestamp = &Convert_To_String($last);
        }
        seek( $fh, $pos, 0 );

        # purge the stats file of obsolete entries
        my $inserted;
        while (<$fh>) {
            if ( $_ =~ /^$dnsname\s+/ ) {
                chomp($_);

                #print LOG "MATCH\n";
                #print LOG "line=$_\n";
                my @stat = split( / /, $_ );

                # previous bindings
                my $port        = $stat[1];
                my $psent       = $stat[2];
                my $precv       = $stat[3];
                my $ptimestamp  = $stat[4] . " " . $stat[5] . " " . $stat[6];
                my $bindings    = $stat[7];
                my $upbindings  = $stat[8];
                my $subscribers = $stat[9];
                my $lasttime    = $stat[10] . " " . $stat[11] . " " . $stat[12];
                chomp($lasttime);
                my $stat =
                    $dnsname . " "
                  . $port . " "
                  . $psent . " "
                  . $precv . " "
                  . $ptimestamp . " "
                  . $bindings . " "
                  . $upbindings . " "
                  . $subscribers . " "
                  . $lasttime;

                # time conversions
                my $T0 = 0;
                if ( $mode == 1 ) {
                    $T0 = poparazzi_convert_to_second($ptimestamp);
                    $T0 = 0 if !defined $T0;
                }
                elsif ( $mode == 2 ) {
                    $T0 = poparazzi_convert_to_second($lasttime);
                }

                if ( $T0 eq $T1 ) {    # if stamp = current timestamp
                    print LOG "keep1: STAT: $stat\n";
                    push( @statistics, $stat );
                    $inserted = 1;
                    next;
                }
                else {
                    # if the port is a stump keep it
                    if ( $port eq "-1/-1" ) {
                        print LOG "keep: STAT: $stat\n";
                        push( @statistics, $stat );
                        $inserted = 1;
                        next;
                    }
                    else {
                        print LOG "purge: STAT: $stat\n";
                        next;
                    }
                }
            }
            elsif ( $_ =~ /^$/ ) {
                next;
            }
            else {
                #print "NO_MATCH\n\n";
                push( @statistics, $_ );
                next;
            }
        }
        close($fh);

        # write out the changes to file
        @statistics = sort(@statistics);
        open( $fh, "+<", $stats_file )
          or die "error: Cannot open $stats_file: $!";
        unless ( flock( $fh, LOCK_EX | LOCK_NB ) ) {
            warn
"$sub: (2) can't immediately write-lock the file ($!), blocking ...";
            unless ( flock( $fh, LOCK_EX ) ) {
                die "$sub: can't get write-lock on numfile: $!";
            }
        }
        seek( $fh, 0, 0 );
        truncate( $fh, 0 );

        my $len = scalar(@statistics);
        foreach my $i ( 0 ... ( $len - 1 ) ) {

            print $fh "$statistics[$i]\n";
        }

        close($fh);

        print LOG "FINISH_PURGING_FILE\n";
        return 1, $last;

    }
    else {
        return 0;
    }
}

#-------------------------------------------------------------------------------

=head3 router_update_device_stats_history($;)

    Updates the statistics history for a router

  Usage:

    my $status = router_update_device_stats_history
        ( $args_href, $fh, $dnsname, $bindings, $upbindings, $subscribers, $timestamp );

=cut

#-------------------------------------------------------------------------------

sub router_update_device_stats_history {

    my $sub = ( caller(0) )[3];
    trace_enter($sub);

    my $args_href   = shift;
    my $fh          = shift;
    my $dnsname     = shift;
    my $bindings    = shift;
    my $upbindings  = shift;
    my $subscribers = shift;
    my $timestamp   = shift;

    my $port  = "-1/-1";
    my $psent = 0;
    my $precv = 0;

    my $timezone   = $args_href->{'timezone'};
    my $stats_file = $args_href->{'stats_file'};

    my $ptimestamp = "00-00-00 00:00:00 $timezone";
    my $stat =
        $dnsname . " "
      . $port . " "
      . $psent . " "
      . $precv . " "
      . $ptimestamp . " "
      . $bindings . " "
      . $upbindings . " "
      . $subscribers . " "
      . $timestamp;
    my @statistics;

    # update existing record
    print LOG
"INFO $sub: DEVICE=$dnsname BINDINGS=$bindings UPBINDINGS=$upbindings SUBSCRIBERS=$subscribers TIMESTAMP=$timestamp\n\n";

  # device entry must pre-exist from packet stats (io collect) and not be purged
  # else if device entries are all purged this update has no records to update
  # because we have no associated port to add a new line.
    print LOG "reading file...\n";

    open( $fh, "<", $stats_file ) or die "error: Cannot open $stats_file: $!";
    unless ( flock( $fh, LOCK_SH ) ) {
        warn
"WARNING $sub: (1) can't immediately read-lock the file ($!), blocking ...";
    }

    my $inserted;
    while (<$fh>) {
        chomp($_);
        if ( $_ =~ /^$dnsname\s+/ ) {
            print LOG "MATCH\n";
            print LOG "line=$_\n";
            my @stat = split( / /, $_ );

         # previous port packet sent/recv/timestamp and last bind/subs timestamp
            my $port       = $stat[1];
            my $psent      = $stat[2];
            my $precv      = $stat[3];
            my $ptimestamp = $stat[4] . " " . $stat[5] . " " . $stat[6];
            my $lasttime   = $stat[10] . " " . $stat[11] . " " . $stat[12];

            # save all of the previous timestamps
            # my $lastT0 = poparazzi_convert_to_second($lasttime);
            # push(@$timestamps,$lastT0);
            $stat =
                $dnsname . " "
              . $port . " "
              . $psent . " "
              . $precv . " "
              . $ptimestamp . " "
              . $bindings . " "
              . $upbindings . " "
              . $subscribers . " "
              . $timestamp;
            print LOG "INFO $sub: update: STAT: $stat\n";
            push( @statistics, $stat );

            # IPC need to change this so it updates IPC array for statistics
            $inserted = 1;
            next;
        }
        elsif ( $_ =~ /^$/ ) {
            next;
        }
        else {
            #print "NO_MATCH\n\n";
            push( @statistics, $_ );
            next;
        }
    }
    close($fh);

    # Add new record however, since we dont have any ports
    # we use stump ports which will be purged
    # when the device has valid ports. the stump ports allow
    #checking bindings and subscriptions
    # when the device has no port data

    push( @statistics, $stat ) if !$inserted;

    # write out the changes to file

    @statistics = sort(@statistics);
    open( $fh, "+<", $stats_file )
      or die "error: Cannot open $stats_file: $!";
    unless ( flock( $fh, LOCK_EX | LOCK_NB ) ) {
        warn
"WARNING $sub: (2) can't immediately write-lock the file ($!), blocking ...";
        unless ( flock( $fh, LOCK_EX ) ) {
            die "FATAL $sub: can't get write-lock on numfile: $!";
        }
    }
    seek( $fh, 0, 0 );
    truncate( $fh, 0 );

    my $len = scalar(@statistics);
    foreach my $i ( 0 ... ( $len - 1 ) ) {
        print $fh "$statistics[$i]\n";
    }
    close($fh);

    print LOG "INFO $sub: FINISH_UPDATING_FILE\n";

    return 1;
}

#-----------------------------------------------------------------------------

# shell wrappers

=head2 Unix Shell Wrappers

    These routines supply an interface to the UNIX
    shell and system calls.

=head3 poparazzi_shell_graceful_exit($;)

    Arguments:

    Returns: 

    This module exits the application and clears the screen
    mostly a placeholder for exits that require more 
    functionality.

=cut

#----------------------------------------

sub poparazzi_shell_graceful_exit () {

    my $sub = ( caller(0) )[3];
    trace_enter($sub);

    system("clear");

    trace_exit($sub);
    exit $false;
}

#---------------------------------------

=head3 poparazzi_shell_local($$;)

    Arguments: $args_href
               $command
    Returns: success: 0
             failure: 1

    Run a command using backticks and return
    $true  on success and $false  on error.

=cut

#---------------------------------------
sub poparazzi_shell_local($$;) {

    my $sub = ( caller(0) )[3];
    trace_enter($sub);

    my $args_href = shift;
    my $cmd       = shift;

    my $trace = $ENV{ECUT_TRACE};

    if ( defined $trace && $trace == 1 ) {
        print " - ";
    }

    my $rc = `$cmd`;

    my $status = $? >> 8;

    if ( $? != 0 ) {

        my $msg = "Execution of $cmd failed.";

        #Log( $args_href, $msg );
        #Warning($msg);
        print "WARN $sub: $msg\n";
        trace_exit($sub);
        return ( $false, $rc );
    }
    if ( defined $trace && $trace == 1 ) {
        print "$cmd.\n";
    }

    trace_exit($sub);
    return ( $true, $rc );
}

#---------------------------------------

=head3 poparazzi_shell_remote($$$;$)

    Arguments: $args_href
               $host
               $command
               $trace_switch

Returns: success: ( $true, $rc );
         failure: ( '$false', $rc );

    Run a remote (ssh) command using ticks and returns
    the value returned from the shell and the exit status.
    Currently only connects to the defined application
    server.

=cut

#---------------------------------------

sub poparazzi_shell_remote($$$;$) {

    my $sub = ( caller(0) )[3];
    trace_enter($sub);

    my $args_href = shift;
    my $host      = shift;
    my $cmd_arg   = shift;
    my $trc_arg   = shift;                      # turn on trace in remote script
    my $tool_ssh  = $args_href->{'tool_ssh'};

    # build the ssh command
    #my $cmd = "su - oracle -c \"$tool_ssh $host $cmd_arg\" ";

    my $cmd = "$tool_ssh $host $cmd_arg";
    my $rc  = `$cmd`;

    if ( $? > 0 ) {
        my $msg = "Remote command failed ( $? ): $cmd";
        $msg .= "Note logging from poparazzi_shell_remote";

        #pop_log( "LOG_WARN", $msg );

        trace_exit($sub);
        return ( $false, $rc );
    }

    trace_exit($sub);
    return ( $true, $rc );
}

# -------------------------------------------------------------------------------

=head2 Ecut Time Routines

=head3 poparazzi_time_convert_to_seconds($;)

    From passing parameter string, which basically a timestamp, convert into seconds
    returns time in offset timezone seconds.

    Usage:

       my $seconds = poparazzi_time_convert_to_seconds($timestamp);

=cut

# -----------------------------------------------------------------------------------------------------

sub poparazzi_time_convert_to_seconds($;) {

    my $sub = ( caller(0) )[3];
    trace_enter($sub);

    my $timestamp = shift;

    my $debug = ( caller(0) )[3] . "(@_)";
    print "$debug\n" if $::DEBUG;

    # convert the string formatted timestamp into seconds
    my $seconds = str2time($timestamp);
    trace_exit($sub);
    return ($seconds);
}

# -----------------------------------------------------------------------------------------------------

=head3 poparazzi_time_convert_to_string($;)

    From passing parameter time which is in seconds, convert to string format
    but will return the timestamp in server timezone (PDT/PST) regardless of timezone ext.

    Parameters  : $seconds - in seconds
    return      : $today - format [HH:MM:SS]

    Usage: 

        my $timestamp = poparazzi_time_convert_to_string($seconds);

=cut

# -----------------------------------------------------------------------------------------------------

sub poparazzi_time_convert_to_string ($;) {

    my $sub = ( caller(0) )[3];
    trace_enter($sub);

    my $seconds = shift;

    my $debug = ( caller(0) )[3] . "(@_)";
    print "$debug\n" if $::DEBUG;

    my $string = strftime( '%Y-%m-%d %H:%M:%S', localtime($seconds) );

    trace_exit($sub);
    return ($string);
}

# -----------------------------------------------------------------------------------------------------

=head3 poparazzi_time_convert_to_string_TZ($$$;)

    Convert the remote seconds back to remote String.
    The goal is to allow poparazzi_time_convert_to_secondss a remote timestamp then use poparazzi_time_convert_to_string_TZ
    to get back to the correct remote timestamp. Then remote time while in seconds can be modified
    then converted back to remote timezone timestamp.

    Parameters  : $seconds - in seconds,
                : $offset in seconds as a signed or unsigned int (25200 -28800) or in abbreviated name (EST, PST).
                : If offset is in seconds its assumed the caller knows his abbreviated timezone. Timezone ext not reterned.
                : If the offset is in abbreviated timezone the timezone is looked up and offset derived. Tiemzone ext is returned.
                : %tztable - The timezone table. The caller must initialize/slurp that table as a hash.

    Return      : $timestamp - (-28800) 2012-05-15 05:00:00 or (EST) 2012-05-15 05:00:00 EST
    Usage: 

        my $str = poparazzi_time_convert_to_string($seconds, $remote_offset, $tz_table );

=cut

# -----------------------------------------------------------------------------------------------------

sub poparazzi_time_convert_to_string_TZ($$$;) {

    my $sub = ( caller(0) )[3];
    trace_enter($sub);

    my $seconds       = shift;
    my $remote_offset = shift;
    my $tztable       = shift;

    # $remote_offset can be an int -28800 or an abbreviated timezone EST/PST
    # my $local_offset = "PDT";
    my $local_offset;

    # in case the caller doesnt set timezone such as util/test scripts
    unless ( $::TIMEZONE || $local_offset ) {
        $local_offset = `date +%Z`;
        chomp($local_offset);
    }
    else {
        $local_offset = $::TIMEZONE;
    }

    unless ($local_offset) {
        trace_exit($sub);
        return 0;
    }
    else {
        #print LOG "LOCAL_TIMEZONE=$local_offset\n";
    }

    # timezone table lookup
    if ($tztable) {

        #print LOG "\nTIMEZONE_TABLE(lookup):\n";
        foreach my $k ( keys %$tztable ) {

            if ( $k eq $local_offset || $k eq $remote_offset ) {

                #print "------------------------------------------------\n";
                #print "$k TIMEZONE=$tztable->{$k}{TIMEZONE}\n";
                #print "$k UTC=$tztable->{$k}{UTC_OFFSET}\n";

                # get the UTC offset, convert to seconds
                my @utc_offset = split( " ", $tztable->{$k}{UTC_OFFSET} );
                my $offset = $utc_offset[1];

                my ( $utc_offset, $sign );
                if ($offset) {

                    # +-hr:mm format
                    if ( $offset =~ /:/ ) {
                        my @hm = split( /:/, $offset );
                        my $h = $hm[0];
                        if ( $h < 0 ) {
                            $h    = abs($h);
                            $sign = "-";
                        }
                        elsif ( $h > 0 ) {
                            $h    = abs($h);
                            $sign = "+";
                        }
                        my $m = $hm[1];
                        $utc_offset = ( $h * 3600 ) + ( $m * 60 );
                        $utc_offset = $sign . $utc_offset;

                        # +-hr format
                    }
                    else {
                        my $h = $offset;
                        if ( $h < 0 ) {
                            $h    = abs($h);
                            $sign = "-";
                        }
                        elsif ( $h > 0 ) {
                            $h    = abs($h);
                            $sign = "+";
                        }
                        $utc_offset = ( $h * 3600 );
                        $utc_offset = $sign . $utc_offset;
                    }

                    #print "$k OFFSET=$utc_offset seconds\n";
                }

                if ( $k eq $local_offset ) {
                    $local_offset = $utc_offset;
                }
                if ( $k eq $remote_offset ) {
                    $remote_offset = $utc_offset;
                }

                #print "------------------------------------------------\n";
            }
        }
    }
    else {
        #print LOG "error: $debug: no tztable data\n";
        trace_exit($sub);
        return 0;
    }

    # diff the two offsets to get final offset, convert to seconds
    my $offset = $local_offset - $remote_offset;
    my $hours  = $offset / 3600;

    print "INPUT seconds=$seconds remote(offset)=$remote_offset ";
    print "local(offset)=$local_offset final(offset)=$offset hours=$hours\n";

    # convert (convert_to_string) seconds to remote time by - its offset.
    if ( $offset == $local_offset ) {
        $seconds = $seconds - $offset;

        #print LOG "remote time is: (UTC/GMT/ZULU) SECONDS_TZ=$seconds\n";
    }
    elsif ($offset) {
        $seconds = $seconds - $offset;

        #print LOG "remote time offset is: SECONDS_TZ=$seconds\n";
    }
    else {
        #print LOG "remote time is: (NO_OFFSET) LOCAL\n";
    }

    # strftime show PDT (server timezone) which is +2 from
    # EST. PST is +3 from EST (+-offset above)
    my $string = strftime( '%Y-%m-%d %H:%M:%S', localtime($seconds) );

    # the remote seconds re-converted back to remote time
    print "TIMESTAMP_TZ(return)=$string\n\n";

    #print LOG "TIMESTAMP_TZ(return)=$string\n\n";

    trace_exit($sub);
    return ($string);
}

# -----------------------------------------------------------------------------------------------------

=head3 poparazzi_time_convert_to_timestamp($;)

    Convert the passing parameter [array] into a formatted timestamp for ECUT syntax
    then return the list of timestamp.

    Usage: 

        my $aref  = poparazzi_time_convert_to_timestamp( $aref );
        my @count = @$aref;

=cut

# -----------------------------------------------------------------------------------------------------

sub poparazzi_time_convert_to_timestamp($;) {

    my $sub = ( caller(0) )[3];
    trace_enter($sub);

    my $aref = shift;
    my @list = @$aref;

    my @newlist;
    foreach my $line (@list) {

        # Format
        # 2011 Jun 1 18:04:09
        #
        my (@stamp) = split( /\s+/, $line );

        # check if YEAR is part of the line else concatenate
        if ( $stamp[0] ne $::SYSTEM_YEAR ) {

            # get the year from the system clock
            $line = $::SYSTEM_YEAR . " " . $line;
        }

        # split it again
        (@stamp) = split( /\s+/, $line );
        my $year = $stamp[0];
        my $month = substr( $line, 6, 3 );
        print "*** Year [$year] Month [$month] ****";
        $month = poparazzi_time_month_to_number( $stamp[1] );

        my $day = $stamp[2];
        my $hr  = $stamp[3];

        my $timestamp = $year . "-" . $month . "-" . $day . " " . $hr;
        print "new timestamp = [$timestamp] \n";

        push( @newlist, $timestamp );

    }

    trace_exit($sub);
    return \@newlist;

}

# -----------------------------------------------------------------------------------------------------

=head3 poparazzi_time_convert_to_UTC_timestamp($;)

    Convert the passing parameter [array] into a formatted timestamp for ECUT syntax
    and convert the UTC timestamp with corrected timezone
    Then return the list of timestamp

    Usage: 

        my $ret_aref = poparazzi_time_convert_to_timestamp( $aref  );
        my @count = @$ret_aref;

=cut

# -----------------------------------------------------------------------------------------------------

sub poparazzi_time_convert_to_UTC_timestamp {

    my $sub = ( caller(0) )[3];
    trace_enter($sub);

    my $aref = shift;

    my @list = @$aref;

    my @newlist;
    foreach my $line (@list) {

        print "line = [$line]";

        # Format
        # 2011 Jun 1 18:04:09
        #
        my (@stamp) = split( /\s+/, $line );

        # check if YEAR is part of the line else concatenate
        #if ($stamp[0] ne $::SYSTEM_YEAR) {
        #    # get the year from the system clock
        #    $line=$::SYSTEM_YEAR." ".$line;
        #}

        # split it again
        (@stamp) = split( /\s+/, $line );
        my $year = $stamp[0];

        #my $month = substr($line, 5, 3);
        my $month = $stamp[1];
        print "year [$year] month [$month]";
        $month = poparazzi_time_month_to_number( $stamp[1] );

        my $day = $stamp[2];
        my $hr  = $stamp[3];

        my $timestamp = $year . "-" . $month . "-" . $day . " " . $hr;
        $timestamp = poparazzi_time_utc_to_local($timestamp);

        push( @newlist, $timestamp );

    }

    trace_exit($sub);
    return \@newlist;
}

# -----------------------------------------------------------------------------------------------------

=head3 poparazzi_time_day_to_string($;)

    Conversion of numeric day to text format

    Parameters  : integer [7]
    return      : $text [Mon]

    Usage: 

        my $day = poparazzi_time_day_to_string($num);

=cut

# -----------------------------------------------------------------------------------------------------

sub poparazzi_time_day_to_string($;) {

    my $sub = ( caller(0) )[3];
    trace_enter($sub);

    my $num      = shift;
    my @weekDays = qw(Sun Mon Tue Wed Thu Fri Sat Sun);

    my $text = $weekDays[ $num - 1 ];

    print "input day $num, output day $text";

    trace_exit($sub);
    return $text;
}

# -----------------------------------------------------------------------------------------------------

=head3 poparazzi_time_delta_day($;)

    Convert given day into formatted date and time

    Parameters  : $day - integer
    return      : hash

    Usage: 

         my $href  = poparazzi_time_delta_day($day);
         my %today = %$href;

=cut

# -----------------------------------------------------------------------------------------------------

sub poparazzi_time_delta_day ($; ) {

    my $sub = ( caller(0) )[3];
    trace_enter($sub);

    my $day = shift;

    my $day_sec          = $day * 24 * 60 * 60;
    my $previous_day_sec = $::SYSTEM_CLOCK - $day_sec;
    my ( $sec, $min, $hour ) = localtime($previous_day_sec);
    my ( $wday, $month_text, $today, $time, $year ) =
      split( /\s+/, scalar( localtime($previous_day_sec) ) );

    #print "sec $sec,min $min,hr $hour,day $today,";
    #print "month $month_text,year $year, weekday $wday\n";
    my $month_numeric = poparazzi_time_month_to_number($month_text);
    my $msg           = "*** sec $sec,min $min,hr $hour,day $today,month ";
    $msg .= "$month_numeric,year $year, weekday $wday ***", print $msg;

    my %delta = (
        SECOND        => $sec,
        MINUTE        => $min,
        HOUR          => $hour,
        YEAR          => $year,
        WEEKDAY       => $wday,
        DAY           => $today,
        MONTH_TEXT    => $month_text,
        MONTH_NUMERIC => $month_numeric
    );

    trace_exit($sub);
    return %delta;
}

#-----------------------------------------------------------------------------------------------------

=head3 poparazzi_time_get_hour_brackets($;)

    Description: take a timestamp and return the begin and end times
    of the hour. It does not return timezone extension regarless if
    provided. However it does return the correct time of the provided timezone.
    if the return timestamps are (witjout timezone ext) is converted to seconds.
    the epoch in time in seconds will be in the timezone of the (this) server
    doing the conversion (PST/PDT).

    Parameters  : $timestamp
                : "2012-05-15 04:21:38 PST" or "2012-05-15 04:21:38" no timezone
    Return      : $begin $end - the start and end of the hour in the timezone of the
                : provided timestamp with no timezone ext.

    Usage:

         

=cut

#-----------------------------------------------------------------------------------------------------

sub poparazzi_time_get_hour_brackets($;) {

    my $sub = ( caller(0) )[3];
    trace_enter($sub);

    my ($timestamp) = shift;

    my ( $ss, $mm, $hh, $day, $month, $year, $zone ) = strptime($timestamp);
    if ( $hh >= 24 ) { return 0, 0 }

    # if $timestamp = "2012-05-15 04:21:38 PST";
    # routine will return seconds=38 minutes=21
    # hours=04 day=15 month=4 year=112 zone=-28800
    # 3600 seconds * -8 hours = -28800 seconds
    # for timezone offset from UTC/GMT/zulu

    # debug
    # print "pop_time_get_hour_brackets: seconds=$ss minutes=$mm hours=$hh ";
    # print "day=$day month=$month year=$year zone=$zone\n";

    $year  = $year + 1900;
    $month = $month + 1;
    my $hhh = ( $hh + 1 );
    if ( $hhh == 24 ) { $hhh = 00; }
    $ss = 00;
    $mm = 00;

    # format the date range
    my $b = sprintf( "%02d-%02d-%02d %02d:%02d:%02d",
        $year, $month, $day, $hh, $mm, $ss );
    my $e = sprintf( "%02d-%02d-%02d %02d:%02d:%02d",
        $year, $month, $day, $hhh, $mm, $ss );

    # check for midnight next day event
    if ( $hhh == 00 ) {
        my $esec = poparazzi_time_convert_to_seconds($e);

        # add one day to date
        $esec = $esec + 86400;
        $e    = poparazzi_time_convert_to_string($esec);
    }

    trace_exit($sub);
    return ( $b, $e );
}

#-----------------------------------------------------------------------------------------------------

=head3 poparazzi_time_get_hour_brackets_TZ($;) 


    Same as poparazzi_time_get_hour_brackets except will preserve the timezone extension
    of the caller) in the results. This allows the caller to re-use the
    returned results in conversion to seconds with correct timezone offset
    to obtain correct epoch time. However for reliability will return both formats.
    without timezone ext in input wil behave like orig poparazzi_time_get_hour_brackets.

    Parameters  : $timestamp
                : "2012-05-15 04:21:38 PST" or "2012-05-15 04:21:38" no timezone
    Return      : $begin $end - the start and end of the hour in the timezone of the
                : provided timestamp with TIMEZONE EXT.

=cut 

#-----------------------------------------------------------------------------------------------------

sub poparazzi_time_get_hour_brackets_TZ($;) {

    my $sub = ( caller(0) )[3];
    trace_enter($sub);

    my $timestamp = shift;

    my ( $ss, $mm, $hh, $day, $month, $year, $zone ) = strptime($timestamp);

    # its not possible to convert numeric timezone offset
    # to the original abbreviated timezone, so we use this
    # method which is standard format within our scripts.

    my @tz = split( / /, $timestamp );
    my $tz = $tz[2];

    if ( $hh >= 24 ) { return 0, 0 }

    # if $timestamp = "2012-05-15 04:21:38 PST";
    # routine will return seconds=38 minutes=21 hours=04 day=15
    # month=4 year=112 zone=-28800
    # 3600 seconds * -8 hours = -28800 seconds for
    # timezone offset from UTC/GMT/zulu

    # debug
    # print "pop_time_get_hour_brackets: seconds=$ss minutes=$mm ";
    # print "hours=$hh day=$day month=$month year=$year zone=$zone\n";

    $year  = $year + 1900;
    $month = $month + 1;
    my $hhh = ( $hh + 1 );
    if ( $hhh == 24 ) { $hhh = 00; }
    $ss = 00;
    $mm = 00;

    # format the date range
    my $b = sprintf( "%02d-%02d-%02d %02d:%02d:%02d",
        $year, $month, $day, $hh, $mm, $ss );
    my $e = sprintf( "%02d-%02d-%02d %02d:%02d:%02d",
        $year, $month, $day, $hhh, $mm, $ss );

    # check for midnight next day event
    if ( $hhh == 00 ) {
        my $esec = poparazzi_time_convert_to_seconds($e);

        # add one day to date
        $esec = $esec + 86400;
        $e    = poparazzi_time_convert_to_string($esec);
    }

    # re-append the orig abbreviated timezone
    if ($tz) {
        $b = $b . " " . $tz;
        $e = $e . " " . $tz;
    }

    trace_exit($sub);
    return ( $b, $e );
}

# -----------------------------------------------------------------------------------------------------

=head3 poparazzi_time_get_timezone_offset($;)

    From passing parameter string, which basically a timestamp
    with timezone "2012-05-15 04:21:38 PST".  Returns time in
    offset timezone seconds 28800 -28800

    Parameters  : $timestamp requiring timezone extension
    Return      : time in seconds

    Usage       : 

        my $secons = poparazzi_time_get_timezone_offset($timestamp);

=cut

# -----------------------------------------------------------------------------------------------------

sub poparazzi_time_get_timezone_offset ($;) {

    my $sub = ( caller(0) )[3];
    trace_enter($sub);

    my $timestamp = shift;

    my ( $ss, $mm, $hh, $day, $month, $year, $zone ) = strptime($timestamp);
    if ( $hh >= 24 ) { return 0, 0 }

    $year  = $year + 1900;
    $month = $month + 1;

    # return the offset in seconds, -seconds

    trace_exit($sub);
    return ($zone);
}

# -----------------------------------------------------------------------------------------------------

=head3 poparazzi_time_get_timestamp($;)

    Get current localtime and convert to formatted timestamp

    Parameters  : None
    Return      : timestamp
    Usage: 

        my $timestamp = poparazzi_time_get_timestamp();

=cut

# -----------------------------------------------------------------------------------------------------

sub poparazzi_time_get_timestamp(;) {

    my $sub = ( caller(0) )[3];
    trace_enter($sub);

    # Added %Z timezone to $tm value below; evugian; 05/16/2012
    my ($tm) = strftime( '%Y-%m-%d %H:%M:%S %Z', localtime );

    my @months   = qw(Jan Feb Mar Apr May Jun Jul Aug Sep Oct Nov Dec);
    my @weekDays = qw(Sun Mon Tue Wed Thu Fri Sat Sun);
    my (
        $second,     $minute,    $hour,
        $dayOfMonth, $month,     $yearOffset,
        $dayOfWeek,  $dayOfYear, $daylightSavings
    ) = localtime();

    my $year    = 1900 + $yearOffset;
    my $theTime = "$hour:$minute:$second, $weekDays[$dayOfWeek] ";
    $theTime .= "$months[$month] $dayOfMonth, $year";

    $::SYSTEM_YEAR  = $year;
    $::SYSTEM_MONTH = $month;
    $::SYSTEM_DAY   = $dayOfMonth;

    trace_exit($sub);
    return $tm;
}

# -----------------------------------------------------------------------------------------------------

=head3 poparazzi_time_month_to_number($;)

    Convert month string to month number

    Parameters  : string [Jul]
    Return      : $local_month [07]2010-09-06 15:06:53]

    Usage: 

        my $month_num = poparazzi_time_month_to_number($string);

=cut 

# -----------------------------------------------------------------------------------------------------

sub poparazzi_time_month_to_number ($;) {

    my $sub = ( caller(0) )[3];
    trace_enter($sub);

    my $local_month = shift;

    my %M = (
        Jan => 1,
        Feb => 2,
        Mar => 3,
        Apr => 4,
        May => 5,
        Jun => 6,
        Jul => 7,
        Aug => 8,
        Sep => 9,
        Oct => 10,
        Nov => 11,
        Dec => 12
    );
    my $mo = $M{$local_month};
    if ( $mo eq "" ) {
        print "????????????????????????????????????";
        print "Wrong MONTH ..... poparazzi_time_month_to_number()";
        print "before conversion = [$local_month] ";
        print "after  conversion = [$mo]";
        print "????????????????????????????????????";
    }

    trace_exit($sub);
    return $mo;
}

# -----------------------------------------------------------------------------------------------------

=head3 poparazzi_time_month_to_string($;)

    Convert month number to month string

    Parameters  : integer [7]
    Return      : $text [Jul]

    Usage: 

        my $month = poparazzi_time_month_to_string($num);

=cut

# -----------------------------------------------------------------------------------------------------

sub poparazzi_time_month_to_string ($;) {

    my $sub = ( caller(0) )[3];
    trace_enter($sub);

    my $num = shift;

    my @abbr = qw( Jan Feb Mar Apr May Jun Jul Aug Sep Oct Nov Dec );
    my $text = $abbr[ $num - 1 ];

    trace_exit($sub);
    return $text;
}

# -----------------------------------------------------------------------------------------------------

=head3 poparazzi_time_get_hour_from_timestamp($;)

    Get hour number from a timestamp

    Parameters  : string (Jul 31 09:50:22)
    return      : hour (09)

    Usage: 

        my $hr = poparazzi_time_get_hour_from_timestamp($line);

=cut

#-----------------------------------------------------------------------------------------------------

sub poparazzi_time_get_hour_from_timestamp($;) {

    my $sub = ( caller(0) )[3];
    trace_enter($sub);

    my $list = shift;
    chomp($list);

    my ( $datehour, $rest ) = split( /:/, $list, 2 );

    #print "datehour [$datehour]  rest [$rest]\n";
    my ( $month, $day, $hour ) = $datehour =~ /(\w+)\s+(\d+)\s+(\d+)/;

    #print "EDSELLL month $month day $day time $hour\n";

    trace_exit($sub);
    return $hour;
}

# -----------------------------------------------------------------------------------------------------

=head3 poparazzi_time_utc_to_local($;)

    Conversion of UTC time to local standard time in string format [text based]

    Parameters  : string [2010-09-06 15:06:53.512999]
    Return      : $timestamp [2010-09-06 15:06:53]

    Usage: 

        my $timestamp = poparazzi_time_utc_to_local($string);

=cut

# -----------------------------------------------------------------------------------------------------

sub poparazzi_time_utc_to_local ($;) {

    my $sub = ( caller(0) )[3];
    trace_enter($sub);

    my $t = shift;

    #print "before utc conversion - [$t]\n";
    #my ($datehour, $min,$rest) = split(/:/,$t,3);

    my ( $datehour, $rest ) = split( /:/, $t, 2 );
    my ( $min, $sec ) = split( /:/, $rest );

    #my ($edhour,$edmin,$edsec, $edrest) = split(/:/,$t,3);
    #print "EDSEL hr $edhour min $edmin sec $edsec rest $edrest\n";

    my ( $year, $month, $day, $hour ) =
      $datehour =~ /(\d+)-(\d+)-(\d+)\s+(\d+)/;

    #  proto: $time = timegm($sec,$min,$hour,$mday,$mon,$year);
    my $epoch = timegm( 0, 0, $hour, $day, $month - 1, $year );

    #  proto: ($sec,$min,$hour,$mday,$mon,$year,$wday,$yday,$isdst) =
    #          localtime(time);
    my ( $lyear, $lmonth, $lday, $lhour, $isdst ) =
      ( localtime($epoch) )[ 5, 4, 3, 2, -1 ];

    $lyear += 1900;    # year is 1900 based
    $lmonth++;         # month number is zero based
    if ($isdst) {
        $::IS_DST = 1;
        my $before = sprintf( "%04d-%02d-%02d %02d:%s",
            $lyear, $lmonth, $lday, $lhour, $rest );

        #print "Before spring forward [$before]\n";
        #print "DST is on... do spring forward of 1HR\n";
        #$lhour++;
    }

    #print "isdst: $isdst\n"; #debug flag day-light-savings time
    $::SYSTEM_YEAR  = $lyear;
    $::SYSTEM_MONTH = $lmonth;
    $::SYSTEM_DAY   = $lday;
    $::SYSTEM_HR    = $lhour;
    $::SYSTEM_MIN   = $min;
    $::SYSTEM_SEC   = $sec;

    #print "utc system_sec  = $::SYSTEM_SEC\n";
    #print "utc system_min  = $::SYSTEM_MIN\n";
    #print "utc SYSTEM_HR = $::SYSTEM_HR\n";
    #print "utc system_day  = $::SYSTEM_DAY\n";
    #print "utc system_month= $::SYSTEM_MONTH\n";
    #print "utc system_year = $::SYSTEM_YEAR\n";

    # return format is the same timestamp format use in ECUT DB
    my $timestamp = sprintf( "%04d-%02d-%02d %02d:%s",
        $lyear, $lmonth, $lday, $lhour, $rest );

    #print "after utc conversion - [$timestamp]\n";
    #return ( sprintf("%04d-%02d-%02d %02d:%02d:%s",
    #         $lyear,$lmonth,$lday,$lhour,$min,$rest) );
    #

    trace_exit($sub);
    return $timestamp;
}

# -----------------------------------------------------------------------------------------------------

=head3 poparazzi_time_validate_router_clock($$$;)

    This subroutine is to validate the router clock vs UTC time. This is needed for
    a wrong timezone configuration.  This is to validate wrongly configured timezone

    Parameters  : $unix_sec = unix time in seconds
                  $router_sec = router time converted in seconds
                  $cap = default to 1 HR = 3600 sec

    Return      : $result,$state

    Usage: 

       my ($rs,$state) =  poparazzi_time_validate_router_clock($unix,$clock,$hr);

=cut

# -----------------------------------------------------------------------------------------------------

sub poparazzi_time_validate_router_clock {

    my $sub = ( caller(0) )[3];
    trace_enter($sub);

    my $unix_sec   = shift;
    my $router_sec = shift;
    my $cap        = shift;

    $cap = 3600 unless defined $cap;
    my $state;
    if ( $router_sec > $unix_sec ) {
        $state = "FORWARD";
    }
    else {
        $state = "BACKWARD";
    }

    my $diff = abs( $unix_sec - $router_sec );

    my $mod = $diff % $cap;
    my $hr  = $diff / $cap;

    if ( $mod == 0 ) {

        # this is perfect hour manipulation by the user
        if ( $state eq "BACKWARD" ) {
            return ( $hr, $state );
        }
        else {
            print
              " WARN  $sub :  Router clock doesn't follow standard time ###";
            return ( 0, "NULL" );
        }
    }
    elsif ( $state eq "BACKWARD" ) {
        print "Modulus is NOT zero [$mod] hr[$hr] state [$state]";
        print "Devices is not connected to NTP server";
        trace_exit($sub);
        return ( 0, $state );

    }
    elsif ( $state eq "FORWARD" ) {
        print "Modulus is NOT zero [$mod] hr[$hr] state [$state]";
        print "Devices is not connected to NTP server";
        trace_exit($sub);
        return ( 0, $state );

    }
    print "Modulus is NOT zero [$mod] hr[$hr] state [$state]";
    trace_exit($sub);
    return ( 0, "NULL" );
}

#-------------------------------------------------------------------------------

=head2 Traffic Generator Routines

=head3 tgen_add_n2x_ports_to_href($$$;)

    Returns device_href

    The $device_href argment is a hash with host metadataa and
    a list of host ports extraced from a csv file returned by a host.

    This routine is used to fill in any missing ports for the host controller.
    Since n2x ports that are not in a session don't return status, the returned
    array reference, supplies the missing ports (and the active ones) to 
    allow the collector to post status on all of the ports on the chassis.
  
    Usage:

        my $device_href = tgen_add_n2x_ports_to_href( $args_href, $dnsname,  $device_href );

=cut

#-------------------------------------------------------------------------------

sub tgen_add_n2x_ports_to_href ($$$;) {

    my $sub = ( caller(0) )[3];
    trace_enter($sub);

    my $args_href   = shift;
    my $dnsname     = shift;
    my $device_href = shift;

    my $assistant_type = 'n2x';

    # make an array of the ports on the chasis.
    #

    #     here is an exmample of the n2x metadata:
    #
    # 'linecard_4102_type' => 'AGT_CARD_EIGHTPORT_10GBASE_R',
    # 'physical_linecards_installed' => '1',
    # 'linecard_4102_ports' => '8',
    # 'linecard_4102_serial_number' => '089509',
    #
    # $device_href->{$dnsname}->{'linecards'}->{$assistant_type}
    #  ->{$card}->{'num_ports'}
    # $device_href->{$dnsname}->{'linecards'}->{$assistant_type}
    #  ->{$card}->{'serial_number'}
    # $device_href->{$dnsname}->{'linecards'}->{$assistant_type}
    #  ->{$card}->{'linecard_type'}
    # $device_href->{$dnsname}->{'physical_linecards_installed'};
    #

    # add the list of all the cards on the host

    my $href = $device_href->{$dnsname}->{'linecards'}->{$assistant_type};
    my @linecards_array = sort keys %$href;

    # make the return array, for all of the ports on the card
    # using a card loop and an inner port loop.

    my @card_port_array;
    my @port_type_array;
    my @card_model_array;
    my @card_sn_array;

    #cardModel         "cardModel" on the TGEN inventory CSV
    #cardSerialNumber  "cardSerialNumber" on the TGEN inventory CSV

    foreach my $card (@linecards_array) {

        # get port attributes

        my $num_ports =
          $device_href->{$dnsname}->{'linecards'}->{$assistant_type}->{$card}
          ->{'num_ports'};
        my $port_type =
          $device_href->{$dnsname}->{'linecards'}->{$assistant_type}->{$card}
          ->{'port_type'};
        my $card_model =
          $device_href->{$dnsname}->{'linecards'}->{$assistant_type}->{$card}
          ->{'linecard_type'};
        my $card_snum =
          $device_href->{$dnsname}->{'linecards'}->{$assistant_type}->{$card}
          ->{'serial_number'};

        # Debug
        #print "num_ports: $num_ports\n";
        #print "port_type: $port_type\n";
        #print "card_model: $card_model\n";
        #print "card_snum: $card_snum\n";

        # fabricate the full list of ports for the card
        # port ids are always contiguous and start at 1

        for ( my $i = 1 ; $i <= $num_ports ; $i++ ) {

            #my $port = "1.$card.$i";
            my $port = "$card.$i";

            # add an entry for each port for $card
            push( @card_port_array,  $port );
            push( @port_type_array,  $port_type );
            push( @card_model_array, $card_model );
            push( @card_sn_array,    $card_snum );
        }
    }

    my $index = 0;
    foreach my $port (@card_port_array) {

        my $port_type  = $port_type_array[$index];
        my $card_model = $card_model_array[$index];
        my $card_snum  = $card_sn_array[$index];
        $index++;

        if ( !$device_href->{$dnsname}->{'ports'}->{$assistant_type}->{$port} )
        {

            # add missing ports as UNUSED

            $device_href->{$dnsname}->{'ports'}->{$assistant_type}->{$port}
              ->{'status'} = 0;
            $device_href->{$dnsname}->{'ports'}->{$assistant_type}->{$port}
              ->{'pop_state'} = "UNUSED";
            $device_href->{$dnsname}->{'ports'}->{$assistant_type}->{$port}
              ->{'comment'} = "PORT NOT IN AN N2X SESSION";

            $device_href->{$dnsname}->{'ports'}->{$assistant_type}->{$port}
              ->{'port_type'} = $port_type;
            $device_href->{$dnsname}->{'ports'}->{$assistant_type}->{$port}
              ->{'card_model'} = $card_model;
            $device_href->{$dnsname}->{'ports'}->{$assistant_type}->{$port}
              ->{'card_snum'} = $card_snum;

            my $comment =
              $device_href->{$dnsname}->{'ports'}->{$assistant_type}->{$port}
              ->{'comment'};
            $comment = "$comment - Port Type: $port_type";
            $device_href->{$dnsname}->{'ports'}->{$assistant_type}->{$port}
              ->{'comment'} = $comment;
            $device_href->{$dnsname}->{'ports'}->{$assistant_type}->{$port}
              ->{'comment'} = $assistant_type;
        }
    }

    @card_port_array                               = sort @card_port_array;
    $device_href->{$dnsname}->{'card_aref'}        = \@linecards_array;
    $device_href->{$dnsname}->{'device_port_aref'} = \@card_port_array;

    trace_exit($sub);
    return $device_href;
}

#-------------------------------------------------------------------------------

=head3 tgen_close_telnet_obj($;)

    closes a telent connection.

    tgen_close_telnet_obj( $telnet_obj );

=cut

#-------------------------------------------------------------------------------

sub tgen_close_telnet_obj {

    my $sub = ( caller(0) )[3];
    trace_enter($sub);

    my $args_href  = shift;
    my $telnet_obj = shift;

    # close connection
    if ( $args_href->{'telnet_package'} eq 'net_telnet' ) {
        $telnet_obj->close();
    }
    else {
        $telnet_obj->hard_close();
    }

    trace_exit($sub);
    return $true;
}

#-------------------------------------------------------------------------------

=head3 tgen_collapse_device_href($$$;)

    Returns an an altered version of device_href without assistant_type field.
    The collapsed hash contains any 'USED' port hrefs, regardless of 
    the assistatnt_type.

    Usage:

        my $device_href = tgen_collapse_device_href( $args_href, $device_href );

=cut

#-------------------------------------------------------------------------------

sub tgen_collapse_device_href ($$;) {

    my $sub = ( caller(0) )[3];
    trace_enter($sub);

    my $args_href   = shift;
    my $device_href = shift;

    my $pop_href = $args_href->{'pop_href'};

    # deep copy of device_href
    my $new_device_href = dclone $device_href;

    foreach my $dnsname ( keys %$device_href ) {

        my $aref           = $pop_href->{$dnsname}->{'pop_port_aref'};
        my @pop_port_array = sort @$aref;

        $aref = $device_href->{$dnsname}->{'assistant_types_aref'};
        my @assistant_types = @$aref;

        foreach my $assistant_type (@assistant_types) {

            $new_device_href->{$dnsname}->{'ports'}->{$assistant_type} =
              undef;
            $new_device_href->{$dnsname}->{'linecards'} = undef;

            foreach my $port (@pop_port_array) {

                # Collapse device_href for port to a
                # single active port_href if one exists

                my $port_href =
                  tgen_identify_active_port( $args_href, $device_href,
                    $dnsname, $port );

                $new_device_href->{$dnsname}->{'ports'} = $port_href;
            }
        }

        # copy the linecards array - the first assistant type as good as any
        my $a_type = $assistant_types[0];
        if ( $device_href->{$dnsname}->{'linecards'}->{$a_type} ) {
            $new_device_href->{$dnsname}->{'linecards'} =
              dclone $device_href->{$dnsname}->{'linecards'}->{$a_type};
        }
    }

    trace_exit($sub);
    return $new_device_href;
}

#-----------------------------------------------------------------------------------------------------

=head3 poparazzi_decompose_module_file ($$;)

    Desc:        Turn a module file into a hash of blocks of source
                 

    Parameters : $args_href, $input_filename

    Return     :  $file_href or $false

    Usage:

        my $file_href = 
            poparazzi_decompose_module_file ( $args_href, $input_filename);


=cut

#-----------------------------------------------------------------------------------------------------

sub poparazzi_decompose_module_file ( $$;) {

    my $sub = ( caller(0) )[3];
    trace_enter($sub);

    my $args_href      = shift;
    my $input_filename = shift;

    # reusable variables
    my ( $msg, $line, $aref, $href, $str, @array );

    # read the module file
    $aref = pop_slurp_file_into_aref($input_filename);
    my @input_file_array = @$aref;

    #
    # do some cleanup on the array, as needed here
    #

    # regularize the search characters '(' and '}'
    foreach (@input_file_array) {
        s/\(/ (/ig   if $_;
        s/ *\(/ (/ig if $_;
    }

    #
    #   Start decomposing the module file into a hash
    #
    #   This parsing strategy assumes that the inputfile has been
    #   run through PerlTidy and that the file has been produced by
    #   poparazzi.  The location of POD directives, use stmts and
    #   opening and closing curly braces can be assumed to be where
    #   they are expected to be.  This is the approach any of the
    #   file altering and scnning functionality will be implemented
    #   in the first release of poparazzi.

    my $i         = 0;
    my $seperator = "^#--------------------";

    my $file_href = {};

    #
    # get the code in each file section and add it to the $file_href
    # the purpose is the break up the file into its parts so each can
    # can be processed sepeartely.
    #

    # typical code looks for a header, then jumps back to the beginning ot that
    # secion with pop() and decrementing the $i index.

    # file header block
    my $search_str = "^=head3 File History";
    my ( $block_aref, $cursor_index ) =
      poparazzi_get_pop_block_by_tag( \@input_file_array, $i, $search_str,
        $seperator );
    $file_href->{'file_header_aref'} = $block_aref;

    # file history block
    $search_str = "^=head3 Module Dependencies";
    ( $block_aref, $cursor_index ) =
      poparazzi_get_pop_block_by_tag( \@input_file_array, $cursor_index,
        $search_str, $seperator );
    $file_href->{'file_history_aref'} = $block_aref;

    # POD depends section block
    $search_str = "^# only globals PLEASE!";
    ( $block_aref, $cursor_index ) =
      poparazzi_get_pop_block_by_tag( \@input_file_array, $cursor_index,
        $search_str, $seperator );
    $file_href->{'pod_depends_aref'} = $block_aref;

    # code depends section block
    #$search_str = "^=head3";
    $search_str = "^=head1 Subroutines";
    ( $block_aref, $cursor_index ) =
      poparazzi_get_pop_block_by_tag( \@input_file_array, $cursor_index,
        $search_str, $seperator );
    $file_href->{'code_depends_aref'} = $block_aref;

    # subroutine section header block
    $search_str = "^=head3";
    ( $block_aref, $cursor_index ) =
      poparazzi_get_pop_block_by_tag( \@input_file_array, $cursor_index,
        $search_str, $seperator );
    $file_href->{'subs_section_header_aref'} = $block_aref;

    #
    #  Scoop up the subroutine blocks and ad the $file_href
    #

    # prep the subroutine data
    #
    # get the lines that start with sub - that's all the subroutine names
    # pop subs have good use of spaces, so the search should be valid
    # for non-pop code, this test will be different - but this is pop only
    my @subroutine_names_array = grep ( /^sub /, @input_file_array );
    my @subroutine_pod_strs_array =
      grep ( /^=head3 .*\(.*\)/, @input_file_array );
    my $sub_pod_count = @subroutine_pod_strs_array;
    my $sub_pod_index = 0;

    # clean up the names
    foreach my $name (@subroutine_names_array) {
        my @parts = split( " ", $name );
        $name = $parts[1];
    }

    $file_href->{'subroutine_count'}         = $sub_pod_count;
    $file_href->{'subroutine_names_aref'}    = \@subroutine_names_array;
    $file_href->{'subroutine_pod_strs_aref'} = \@subroutine_pod_strs_array;

    foreach my $pod_line (@subroutine_pod_strs_array) {

        $sub_pod_index++;
        my @parts = split( " ", $pod_line );
        my $sub_name = $parts[1];

        $file_href->{'subroutines'}->{$sub_name}->{'pod_line'} = $pod_line;

        # go after the subroutine blocks.

        if ( $sub_pod_index == $sub_pod_count ) {

            # if this is the last subroutine, then account for the file footer
            ( $block_aref, $cursor_index ) =
              poparazzi_get_pop_subroutine_block( \@input_file_array,
                $cursor_index );

            $file_href->{'subroutines'}->{$sub_name}->{'code_block_aref'} =
              $block_aref;
            last;
        }

        ( $block_aref, $cursor_index ) =
          poparazzi_get_pop_subroutine_block( \@input_file_array,
            $cursor_index );
        $file_href->{'subroutines'}->{$sub_name}->{'code_block_aref'} =
          $block_aref;
    }

    # finally get the file footer

    $search_str = "'1;    # always the last line in any Perl module file";
    ( $block_aref, $cursor_index ) =
      poparazzi_get_pop_block_by_tag( \@input_file_array, $cursor_index,
        $search_str, $seperator );
    $file_href->{'file_footer_aref'} = $block_aref;

    trace_exit($sub);
    return $file_href;
}

#-------------------------------------------------------------------------------

=head3 tgen_get_device_utilization_logs( $$;)

  Returns the conents of individual log files on a resource /
  host as elements in an array . Each element is one string,
  containing xml tags / values from a log file
  .

  The routine essentialy serializes an xml log file on a resource into a string
  and adds it as an element in an array, which is returned as an aref .

  Usage :

      my ( $xml_aref, $names_aref ) =
          tgen_get_device_utilization_logs( $args_href, $dnsname );

=cut

#-------------------------------------------------------------------------------

sub tgen_get_device_utilization_logs($$;) {

    my $sub = ( caller(0) )[3];
    trace_enter($sub);

    my $args_href = shift;
    my $dnsname   = shift;

    my $logfile_path   = $args_href->{'utilization_log_path'} . "\\*";
    my $logfile_suffix = $args_href->{'utilization_suffix'};

    my ( $cmd, $aref, @filename_array, $msg );

    #
    # get a list of files on the resource/host $log_path
    #

    $cmd = "get_filenames_by_folder $logfile_path";
    $aref = tgen_send_cmd_to_host( $args_href, $dnsname, $cmd );

    # if no filenames returned, probably means the server is
    # not running on the remote host
    # return undefined values
    return ( $false, $false ) if !$aref;

    #type
    # pull out the directory and subdirecory dots
    # pull out out of date files: collector is
    # run at one hour intervals (hard coded )
    foreach my $name (@$aref) {

        # skip anything that isn't a csv file
        next if $name !~ "\.csv\$";

        # get files from the date and time period of interest
        # by comparing stripped timestamp and file names

        my ( $date, $time, $suffix ) = split( /_/, $name );
        my $file_magnatude      = $date . $time;
        my $time_interval_start = $args_href->{'time_interval_start'};
        my $time_interval_end   = $args_href->{'time_interval_end'};

        # skip any files that are more than one hour old
        next if $file_magnatude < $time_interval_start;
        next if $file_magnatude > $time_interval_end;

        push( @filename_array, $name );
    }

    my $array_size = @filename_array;
    if ( $array_size == 0 ) {

        # Nothing returned from the controller
        # so just return and record the dnsname
        # for the admin email

        return ( $false, $false );
    }

    #
    # use the file list to get the utilization data
    #

    my @ret_array;

    foreach my $fname (@filename_array) {

        # "_ecut.csv" for log files
        next if $fname !~ /$logfile_suffix/;    # created above

        my $file_contents_aref;
        @$file_contents_aref = ();

        my $path = $args_href->{'utilization_log_path'};
        my $file = "$path/$fname";

        $cmd = "get_file_by_name $file";

        $file_contents_aref =
          tgen_send_cmd_to_host( $args_href, $dnsname, $cmd );

        # add device name - which usualy is missing from the csv file
        push( @$file_contents_aref, "dnsname (from collector): $dnsname" );

        # push log contents file as aref
        push( @ret_array, $file_contents_aref );

        # archive the file contents locally
        # if the -l flag was used
        my $archive_dir = $args_href->{'utilization_archive_dir'};
        if ( $args_href->{'log_arg'} ) {

            my $arch_filename = "$archive_dir/$fname";
            if ( -e $arch_filename ) {
                unlink $arch_filename;
            }

            open( FILE, ">$arch_filename" )
              or die "couldn't open $arch_filename";

            foreach my $line ( sort @$file_contents_aref ) {
                print FILE "$line\n";    # copy to archive directory
            }
            close(FILE);                 # and close

            my $msg = "Capturing log file to $arch_filename";
            print "$msg\n";
        }
    }

    # Data Structure Note: @ret_array and @filename_array
    # @ret_array is an array of arrays: each sub-array containis the contents
    # of one file. The @filename array is an ordered list of the filenames.
    # The two are sync'ed: that is, the first @ret_array element is an array
    # of the contents of the file named by the first element in @filename_array
    # - this may be bit too complex for what it does.

    trace_exit($sub);
    return \@ret_array, \@filename_array;
}

#-------------------------------------------------------------------------------

=head3 tgen_get_pop_device_list($$$;) 

    Gets a list of device hostnames to process from the ECUT database based
    on the site and the resource type.

    Usage:

        my ($dnsname_aref, $dnsname_port_href = 
           tgen_get_pop_device_list( $pop_server, $resource_type, $site );

=cut

#-------------------------------------------------------------------------------

sub tgen_get_pop_device_list($$$;) {

    my $sub = ( caller(0) )[3];
    trace_enter($sub);

    my $server        = shift;
    my $resource_type = shift;
    my $site          = shift;

    # define some reusable and return variables
    my ( $aref, $dnsname_aref, $href, $name_port_href );

    my $query_aref =
      poparazzi_get_resources_by_type( $server, $resource_type, $site );

    if ( !$query_aref or @$query_aref == 0 ) {
        print
          "FATAL $sub: no '$resource_type' devices returned from ($server)\n";
        trace_exit($sub);
        exit;
    }

    if ( $resource_type eq 'tgen-ports' ) {

        foreach my $href (@$query_aref) {    # get back an array ref of hrefs

            my $dnsname  = $href->{DNSNAME};
            my $portname = $href->{PORTNAME};

            my $assistant_type = 'n2x';
            $name_port_href->{$dnsname}->{'ports'}->{$assistant_type}
              ->{$portname} = $portname;

            $assistant_type = 'ixia';
            $name_port_href->{$dnsname}->{'ports'}->{$assistant_type}
              ->{$portname} = $portname;

            chomp $dnsname;

            # keep duplicates out of the array
            if ( !grep( /^$dnsname$/, @$dnsname_aref ) ) {
                push( @$dnsname_aref, $dnsname );
            }
        }

    }
    else {

        foreach my $dnsname (@$query_aref) {    # get back an array ref of hrefs

#my $dnsname  = $href->{DNSNAME};
#my $portname = $href->{PORTNAME};
#$name_port_href->{$dnsname}->{'ports'}->{$resource_type}->{$portname} = $portname;

            push( @$dnsname_aref, $dnsname );
        }

    }

    # get unique dnsname list
    my @dnsname_array = keys %$name_port_href;
    @dnsname_array = sort @dnsname_array;

    if (   $resource_type eq 'ssr'
        or $resource_type eq 'se'
        or $resource_type eq 'smartedge' )
    {
        @$dnsname_aref  = sort @$query_aref;    # just rename
        $name_port_href = undef;
    }

    # return an array of unique dnsnames and array
    # of hashes of resources

    trace_exit($sub);
    return ( $dnsname_aref, $name_port_href );
}

#-------------------------------------------------------------------------------

=head3 tgen_get_utilization_csv_file($$$;) 

    Gets a the utilization report csv file from the ECUT webservice
    based on the site and the resource type.

    Usage:

        my ($dnsname_aref, $dnsname_port_href = 
           tgen_get_utilization_csv_file( $pop_server, $resource_type, $site );

=cut

#-------------------------------------------------------------------------------

sub tgen_get_utilization_csv_file($$$;) {

    my $sub = ( caller(0) )[3];
    trace_enter($sub);

    my $server        = shift;
    my $resource_type = shift;
    my $site          = shift;

    # reusable and return variables
    my ( $aref, $dnsname_aref, $href, $name_port_href );

    my $query_aref =
      poparazzi_get_csv_utilization_report_by_type( $server, $resource_type,
        $site );

    if ( !$query_aref or @$query_aref == 0 ) {
        print
          "FATAL $sub: no '$resource_type' devices returned from ($server)\n";
        trace_exit($sub);

        #return $false;
        exit;
    }

    foreach my $href (@$query_aref) {    # get back an array ref of hrefs

        my $dnsname  = $href->{DNSNAME};
        my $portname = $href->{PORTNAME};

        my $assistant_type = 'n2x';
        $name_port_href->{$dnsname}->{'ports'}->{$assistant_type}->{$portname}
          = $portname;

        $assistant_type = 'ixia';
        $name_port_href->{$dnsname}->{'ports'}->{$assistant_type}->{$portname}
          = $portname;

        push( @$dnsname_aref, $dnsname );
    }

    # get unique dnsname list
    my @dnsname_array = keys %$name_port_href;
    @dnsname_array = sort @dnsname_array;

    # return an array of unique dnsnames and array
    # of hashes of resources

    trace_exit($sub);
    return ( \@dnsname_array, $name_port_href );
}

#-----------------------------------------------------------------------------------------------------

=head3 tgen_identify_active_port($$$$;)

    Inferrs from port details, which port reflects the utilization state of the chassis

    Return :      $port_href of the inferred active port

    Usage:   my $port_href  = 
                  tgen_identify_active_port( $args_href, $device_href, $dnsname, $port);       
=cut

#-----------------------------------------------------------------------------------------------------

sub tgen_identify_active_port($$$$;) {

    my $sub = ( caller(0) )[3];
    trace_enter($sub);

    my $args_href   = shift;
    my $device_href = shift;
    my $dnsname     = shift;
    my $port        = shift;

    my $aref      = $device_href->{$dnsname}->{'assistant_types_aref'};
    my $found     = $false;
    my $port_href = undef;

    foreach my $assistant_type (@$aref) {

        # a simple test to see if any of assistant_type ports are marked 'USED'
        #
        $port_href =
          $device_href->{$dnsname}->{'ports'}->{$assistant_type}->{$port};

        my $pop_state = $port_href->{'pop_state'};

        if ( $pop_state eq 'USED' ) {
            $found = $true;
            last;
        }
    }

    trace_exit($sub);
    return ($port_href);
}

#-------------------------------------------------------------------------------

=head3 tgen_n2x_port_is_virtual ( $$$; );

    returns $true or $false if n2x port is vitual

    Usage:

        my $is_virtual = tgen_n2x_port_is_virtual ( $args_href, $port, $assistant_type );


=cut

#-------------------------------------------------------------------------------

sub tgen_n2x_port_is_virtual ($$$;) {

    my $sub = ( caller(0) )[3];
    trace_enter($sub);

    my $args_href      = shift;
    my $port           = shift;
    my $assistant_type = shift;

    return $false if $assistant_type ne "n2x";

    if (    $port > $args_href->{'n2x_virtual_port_range_floor'}
        and $port < $args_href->{'n2x_virtual_port_range_ceiling'} )
    {

        trace_exit($sub);
        return $true;
    }

    trace_exit($sub);
    return $false;
}

#-------------------------------------------------------------------------------

=head3 tgen_n2x_prepare_data_for_post($$$;)

    Configure the $device_href data structure to have all the details for
    posting to ECUT and generating the admin email. This will include, ports
    that are not in an n2x session and metadata about the cards.

    Usage:

       $device_href = 
          tgen_n2x_prepare_data_for_post( $args_href, $dnsname, $device_href );

=cut

#-------------------------------------------------------------------------------

sub tgen_n2x_prepare_data_for_post( $$$;) {

    my $sub = ( caller(0) )[3];
    trace_enter($sub);

    my $args_href   = shift;
    my $dnsname     = shift;
    my $device_href = shift;

    my $assistant_type = 'n2x';

    #
    # Add missing ports to $device_href.
    #
    #   ports that are not in a session, are not returned
    #   as part of the csv file from the device.
    #   To add these ports to ECUT, they need to be inferred
    #   from knowledge of what ports are known to exist on
    #   the device: this is information returned in the csv file.
    #

    # Add all the n2x ports to $device_href - including
    # ports that are not in an N2X session.  Only N2X ports
    # in a session will be available in the log files from
    # the host.  Here we generate device_href entries for
    # missing ports by looking at the linecard information.
    $device_href =
      tgen_add_n2x_ports_to_href( $args_href, $dnsname, $device_href );

    trace_exit($sub);
    return $device_href;
}

# -----------------------------------------------------------------------------------------------------

=head3 tgen_parse_csv_file_aref($$$$;)

    Function    : tgen_parse_csv_file_aref
    Description : Convert the csv aref from the contorller into the device_href.
    Parameters  : an aref of the contents of a csv file
    return      : device_href - holds  details on the specific device
    Usage       : my $device_href = tgen_parse_csv_array($args_href, $csv_file_aref, $device_href );
    Keywords    : tgen

    Notes:

         This routine takes an array where each element is a line of
         comma separated values and stuffs the device_href.  
         The routine is entered once for each dnsname, and iteratively
         loads parsed data into the device_href.

=cut

# -----------------------------------------------------------------------------------------------------

sub tgen_parse_csv_file_aref ($$$$;) {

    my $sub = ( caller(0) )[3];
    trace_enter($sub);

    my $args_href     = shift;
    my $dnsname       = shift;
    my $csv_file_aref = shift;
    my $device_href   = shift;

    # get the assistant_type for the csv file
    # so its clear what type of ports are being processed
    my ($ctype_str) = grep( /controller_type/, @$csv_file_aref );
    if ( !$ctype_str ) {
        my $msg = "no 'assistant_type' value found in csv file";
        print "FATAL $sub: $msg\n";
        exit;
    }

    # pull out the assistant_type ('n2x' or 'ixia' )
    # gets added to the hash for each port
    my @array          = split( /,/, $ctype_str );
    my $ctype          = $array[1];
    my $assistant_type = $ctype;

    # store the assistant_type if unique
    my $aref = $device_href->{$dnsname}->{'assistant_types_aref'};
    my ($atype_str) = grep( /$assistant_type/, @$aref );
    if ( !$atype_str ) {
        push( @$aref, $assistant_type );
    }
    $device_href->{$dnsname}->{'assistant_types_aref'} = $aref;

    # get the config_mode for the csv file
    # so the code can check for conection problems with
    # the chassis
    my ($cmode_str) = grep( /config_mode/, @$csv_file_aref );
    if ( !$cmode_str ) {
        my $msg = "no 'config_mode' value found in csv file";
        print "FATAL $sub: $msg\n";
        exit;
    }

    # pull out the config_mode ('FUSION' or 'STANDALONE' )
    # gets added to the hash for each port
    @array = split( /,/, $cmode_str );
    my $config_mode = $array[1];

    if ( $config_mode eq 'FUSION' ) {
        my ($error_in_log) = grep( /ERROR:/, @$csv_file_aref );

        if ($error_in_log) {
            $device_href->{$dnsname}->{'error_in_log'} = $error_in_log;
        }
    }

    #
    # MAIN loop for parsing the CSV files
    #
    # go through the aref line by line - the aref is
    # an ordered list of the lines in a log file.
    #
    # The log files have hardware details lines, and lines
    # that hold the results of the checks the assistant
    # sofware makes on the chassis to see if it is utilized
    #

    foreach my $line (@$csv_file_aref) {
        chomp $line;
        next if !$line or $line eq '';

        my ( $key, $val, $comment ) = split( /,/, $line );

        if ( !defined $comment ) {
            ( $key, $comment ) = split( /,/, $line );

            #$val = undef;
        }

        chomp $key if $key;
        chomp $val if $val;
        next if !$key or $key eq '';

        #
        # Handle lines that are NOT  _pop_check's
        #
        if ( $key !~ /_pop_check_/ ) {

            # add the non-check linecard metadata to the device_href
            #
            # linecard example
            #
            # 'linecard_4102_type' => 'AGT_CARD_EIGHTPORT_10GBASE_R',
            # 'physical_linecards_installed' => '1',
            # 'linecard_4102_ports' => '8',
            # 'linecard_4102_serial_number' => '089509',

            # break out the parts of the line/key

            my ( $prefix, $card, $attr ) = split( /_/, $key );
            chomp $prefix if $prefix;
            chomp $card   if $card;
            chomp $attr   if $attr;

            if ( $assistant_type eq 'n2x' && $card ) {

                # n2x - continue processing $card
                next if $card !~ /^\d+$/;

                my @slot_array = split( //, $card );
                my $s_size = @slot_array;      # based on numbrers in string
                my $zero   = $slot_array[0];
                my $one    = $slot_array[1];
                my $two    = $slot_array[2];
                my $three = $slot_array[3] if $s_size == 4;

                my ( $ret_str, $chassis, $slot );

                if ( $s_size == 4 ) {          # 4111.1
                    $chassis = $zero . $one;          # dot joins
                    $slot    = $two . $three;
                    $slot    = $three if $two == 0;
                }
                else {                                # 201.1
                    $chassis = $zero;
                    $slot    = $one . $two;
                    $slot    = $two if $one == 0;
                }
                $card = "$chassis.$slot";
            }

            # DEBUG
            #print "p: $prefix, c: $card, a: $attr\n";

            # number of ports
            if ( $card && $card ne '' && $attr && $attr eq 'ports' ) {
                $device_href->{$dnsname}->{'linecards'}->{$assistant_type}
                  ->{$card}->{'num_ports'} = $val;
            }

            # serial number
            if ( $card && $card ne '' && $attr && $attr eq 'serial' ) {
                $device_href->{$dnsname}->{'linecards'}->{$assistant_type}
                  ->{$card}->{'serial_number'} = $val;
            }

            # linecard type
            if ( $card && $card ne '' && $attr && $attr eq 'type' ) {

                $val =~ s/ /_/g;
                $device_href->{$dnsname}->{'linecards'}->{$assistant_type}
                  ->{$card}->{'linecard_type'} = $val;

                # get portType directly from $args_href. The card
                # model/type mapping is configured in the collector
                # 'ini' file.

                # need to replace spaces with underscores in the
                # card type returned from the assistant software
                $val =~ s/ /_/g;
                my $lowercase_cardModel = lc $val;
                my $port_tag = $args_href->{"lc_$lowercase_cardModel"};
                if ( !$port_tag ) {
                    print "WARN $sub: could not resolve cardModel: " . $val
                      . "\n";
                    print $val
                      . "  may be missing from the collector 'ini' file.\n";
                    $device_href->{$dnsname}->{'linecards'}->{$assistant_type}
                      ->{$card}->{'port_type'} =
                      "UNDEFINED IN COLLECTOR INI FILE";
                }
                else {
                    my $uppercase_portType = uc $port_tag;
                    $device_href->{$dnsname}->{'linecards'}->{$assistant_type}
                      ->{$card}->{'port_type'} = $uppercase_portType;
                }
            }

            # physical line cards installed
            if ( $prefix and $prefix eq 'physical' ) {
                $device_href->{$dnsname}->{'physical_linecards_installed'} =
                  $val;
            }

            # virtual linecards
            if ( $prefix and $prefix eq 'virtual' ) {
                $device_href->{$dnsname}->{'virtual_linecards_installed'} =
                  $val;
            }

            # collector version ixia or n2x - eg: 'n2x_assistant_version'
            if ( $attr and $attr eq 'version' ) {
                my $version_name = $assistant_type . "_assistant_version";
                $device_href->{$dnsname}->{$version_name} = $val;
            }

            # chassis_serial_number
            if ( $key and $key eq 'chassis_serial_number' ) {
                $device_href->{$dnsname}->{'chassis_serial_number'} = $val;
            }

            # config_mode
            if ( $key and $key eq 'config_typ' ) {
                $device_href->{$dnsname}->{'config_mode'} = $val;
            }
        }
        else {

            # Add the poparazzi_check values by ports
            # and set the status

            my ( $pop_state, $status, $ret_comment );

            my ( $port, $check_num ) = split( /_pop_check_/, $key );

            #
            # Translate N2X ports to Ixia Port Format (1.1.1)
            # inferes controller type from the format of $port
            #

            # check if its virtual, before we translate to csp format
            next
              if tgen_n2x_port_is_virtual( $args_href, $port, $assistant_type );

            $port = tgen_translate_port_to_csp_format($port);

            # may have a string instead of a status value
            $val = undef if $val ne 0 and $val ne 1;

            my $check_aref =
              $device_href->{$dnsname}->{'ports'}->{$assistant_type}->{$port}
              ->{'check_aref'};

            my $aref_size = 0;
            $aref_size = @$check_aref if $check_aref;

            if ( $check_aref and $aref_size > 0 ) {
                ( $pop_state, $status, $ret_comment ) =
                  tgen_summarize_port_state( $args_href, $assistant_type,
                    $check_aref );
                $val = $status if !defined $val;
            }

            # even though the controller returns status, keep the check
            # for auditing - $val is the status returned from the controller
            # here the code records a positive status when there is one

            if ( $val and $val == 1 ) {

                push( @$check_aref, $comment );
                $device_href->{$dnsname}->{'ports'}->{$assistant_type}->{$port}
                  ->{'status'} = $val;
                $device_href->{$dnsname}->{'ports'}->{$assistant_type}->{$port}
                  ->{'pop_state'} = $pop_state;
                $device_href->{$dnsname}->{'ports'}->{$assistant_type}->{$port}
                  ->{'comment'} = $ret_comment;
                $device_href->{$dnsname}->{'ports'}->{$assistant_type}->{$port}
                  ->{'check_aref'} = $check_aref;
                $device_href->{$dnsname}->{'ports'}->{$assistant_type}->{$port}
                  ->{'assistant_type'} = $assistant_type;
            }
            else {
                push( @$check_aref, $comment );

                #$device_href->{$dnsname}->{'ports'}->{$assistant_type}->{$port}
                #    ->{'status'} = $val;
                $device_href->{$dnsname}->{'ports'}->{$assistant_type}->{$port}
                  ->{'check_aref'} = $check_aref;
                $device_href->{$dnsname}->{'ports'}->{$assistant_type}->{$port}
                  ->{'assistant_type'} = $assistant_type;
            }
        }
    }

    trace_exit($sub);
    return $device_href;
}

#-------------------------------------------------------------------------------

=head3 tgen_print_audit_and_continue($$;)

    This routine print out the device_href datastructure for examination.
    This datastructure represents the information that would have been
    posted to ECUT if the audit flag had not been set.

    Usage:

        $device_href = tgen_print_audit_and_continue( $args_href, $device_href );

=cut

#-------------------------------------------------------------------------------

sub tgen_print_audit_and_continue ($$;) {

    my $sub = ( caller(0) )[3];
    trace_enter($sub);

    my $args_href   = shift;
    my $device_href = shift;

    if ( $args_href->{'audit_arg'} ) {

        #
        # this dumps out the device_href just prior to posting to ECUT
        # the purpose is allow visual inspection of the data for any
        # to be posted
        #

        # don't comment out, this is supposed to be here
        print "\n\n        AUDIT DEVICE HASH (device_href):\n\n";
        ref_dump($device_href);
        print "\n";

        # audit_arg doesn't post to the website
        # just dumps the runtime data hashes
        trace_exit($sub);
        return $true;
    }
}

#-------------------------------------------------------------------------------

=head3 tgen_print_xml_and_continue($$;)

    This routine print out the 'collapsed' device_href datastructure as xml.
    This datastructure represents the information that would have been
    posted to ECUT if the xml flag had not been set.  Unlike the audit flag,
    the device_href has been collapsed, which means that it doesn't have
    assistant_type entries, and the other difference is that the ouput is in xml.  

    The --xml commandline argument is used by tools that want to use the
    audit output for other tasks, and capture the collector output as
    xml.  See XML::Hash.pm.

    Usage:

        my $status = tgen_print_xml_and_continue( $args_href, $device_href );

=cut

#-------------------------------------------------------------------------------

sub tgen_print_xml_and_continue ($$;) {

    my $sub = ( caller(0) )[3];
    trace_enter($sub);

    my $args_href   = shift;
    my $device_href = shift;

    my $collector_script = $args_href->{'tgen_collector_script_path'};

    # NOTE: don't return a collapsed $device_href, there are differences
    # the collapsed hash is the data that is postede to ecut
    $device_href = tgen_collapse_device_href( $args_href, $device_href );

    if ( $args_href->{'xml_arg'} ) {

        #
        # this dumps out the device_href just prior to posting to ECUT
        # the purpose is allow visual inspection of the data for any
        # to be posted
        #
        my $xml_converter = XML::Hash->new();

        my %hash = %$device_href;

        #my $xml_str = $xml_converter->fromHashtoXMLString(%hash);
        my $xml_str = $xml_converter->fromHashtoXMLString($device_href);

        # dump to STDOUT
        print STDOUT "$xml_str";

        # to get the hash back, a tool would use something like this
        # my $xml_href      = $xml_converter->fromXMLStringtoHash($xml_str);

        # xml_arg doesn't post to the website
        # just dumps the runtime data hashe

        trace_exit($sub);
        return $true;
    }
}

#-------------------------------------------------------------------------------

=head3 tgen_prepare_host_data_for_post($$$;)

    This routine handles any platform dependencies related to posting status
    to ECUT.  Each platform will have unique prep requirments; thes reqs have
    been consolodated into this and supliementary routines.

    NOTE:  takes $device_href as an argument and returns the prepared $device_href;

    Usage:

        $device_href = tgen_prepare_host_data_for_post ( $args_href, $dnsname, $device_href );

=cut

#-------------------------------------------------------------------------------

sub tgen_prepare_host_data_for_post($$$;) {

    my $sub = ( caller(0) )[3];
    trace_enter($sub);

    my $args_href   = shift;
    my $dnsname     = shift;
    my $device_href = shift;

    my $pop_stats      = 0;
    my $device_stats   = 0;
    my $metadata       = "";
    my $message        = "";
    my $import_message = "";

    #
    # performa any platform specific processing
    # device_href will be undefined if ping failed
    #

    my $resource_type   = $args_href->{'resource_type'};
    my $site            = $args_href->{'site_location'};
    my $stakeholder     = $args_href->{'stakeholder'};
    my $aref            = $device_href->{$dnsname}->{'assistant_types_aref'};
    my @assistant_types = @$aref;

    $device_href =
      tgen_n2x_prepare_data_for_post( $args_href, $dnsname, $device_href )
      if $device_href;

    #
    # the ECUT port hash is  paired to the device_href argument
    # poparazzi_href is initialized in init_common_data()
    # and is the list of ports, as known to the ecut database
    # as opposed to the ports known to the assistant on the chassis.
    #
    my $pop_href = $args_href->{'pop_href'};
    my $port;

    #
    # ECUT:  get the array of ECUT ports for $dnsname
    #
    my $pop_port_aref  = $pop_href->{$dnsname}->{'pop_port_aref'};
    my @pop_port_array = sort @$pop_port_aref;

   #
   # CONTROLLER: get the array of device ports for $dnsname
   #
   # get a list of all of the ports.  Assuming that any assistant type will have
   # a full list of ports.  This assumption should be watched.
    my $port_href =
      $device_href->{$dnsname}->{'ports'}->{ $assistant_types[0] };
    my @device_port_array = keys %$port_href;
    @device_port_array = sort @device_port_array;

    #
    # PROCESSING SECTION:
    # go through the cases and conditions for posting to ECUT
    #
    #

    #
    # CASE 0:  telnet failure.
    #
    # The device was unreachable for some reason and has
    # a 'ping_status' of $false - set all the
    # ecut ports for that device to DOWN
    #

    if ( !$device_href->{$dnsname}->{'ping_status'} ) {

        foreach my $assistant_type (@assistant_types) {

            foreach $port (@pop_port_array) {    # scan ecut ports

                my $comment = "HOST PING FAILED";

                $device_href->{$dnsname}->{'ports'}->{$assistant_type}->{$port}
                  ->{'status'} = 0;
                $device_href->{$dnsname}->{'ports'}->{$assistant_type}->{$port}
                  ->{'pop_state'} = "DOWN";
                $device_href->{$dnsname}->{'ports'}->{$assistant_type}->{$port}
                  ->{'comment'} = $comment;

            }
        }

        # done
        trace_exit($sub);
        return ( $device_href, 0, 0 );
    }

    # CASE 1:  collector failure
    #
    # Something may be wrong with the data we are getting from
    # the collector script.  Put those checks here
    #
    {
        #
        # test if the software version on the controller is out of date
        # 'minimum_assistant_versions' is set in the master.ini file
        #

        # host version comes from the controller
        foreach my $assistant_type (@assistant_types) {

            my $av_tag = $assistant_type . "_assistant_version";

            my $host_version = $device_href->{$dnsname}->{$av_tag};

            next if !$host_version;    # one will be undef if not Dual mode

            my @array = split( " ", $host_version );
            $host_version = $array[0];

            chomp $host_version;

           # minumum version is set in the ini file for $resource_type collector

            my $minimum_version = $args_href->{'minimum_assistant_version'};

            if ( $host_version < $minimum_version ) {

                my $root = $args_href->{'pop_root'};

                # set it as out of date - used in application file
                $device_href->{$dnsname}->{'backlevel_assistant_version'} =
                  $host_version;

                my $comment = "Found out-of-date assistant software ";
                $comment .= "($host_version) on $assistant_type server";

                foreach $port (@pop_port_array) {    # scan ecut ports

                    $device_href->{$dnsname}->{'ports'}->{$assistant_type}
                      ->{$port}->{'status'} = 0;
                    $device_href->{$dnsname}->{'ports'}->{$assistant_type}
                      ->{$port}->{'pop_state'} = "DISABLED";
                    $device_href->{$dnsname}->{'ports'}->{$assistant_type}
                      ->{$port}->{'comment'} = $comment;
                }

                my $stat =
                  poparazzi_mail_log_to_file_attachment( $args_href, $message );

                $message = undef;    # acting like its a global?
                trace_exit($sub);
                return ( $device_href, $pop_stats, $device_stats );
            }
        }
    }

    #
    # CASE 2:  there are ECUT ports missing from
    #          the device.
    #
    # Post those ports to ECUT as DISABLED.
    # and add to the ECUT admin mail message.
    #

    my $comment = "";

    foreach my $assistant_type (@assistant_types) {
        foreach $port (@pop_port_array) {

            # there may be vitual ports in ECUT
            if (
                tgen_n2x_port_is_virtual( $args_href, $port, $assistant_type ) )
            {
                $message .= "$dnsname,$resource_type,[$port]\n";
                $device_stats++;
                next;
            }

            if ( !grep( /^$port$/, @device_port_array ) ) {

                # if card is not known to device it is a missing card
                # if card is known, but not port, it doesn't exit

                my ( $dontcare, $card, $doesntmatter ) = split( /\./, $port );
                my $card_aref =
                  $device_href->{$dnsname}->{'linecards'}->{$assistant_type}
                  ->{'card_aref'};
                if ( !grep( /^$card$/, @$card_aref ) ) {

                    $comment = "LINECARD DOES NOT EXIST ON CONTROLLER";
                }
                else {
                    $comment = "PORT DOES NOT EXIST ON LINECARD";
                }

                $device_href->{$dnsname}->{'ports'}->{$assistant_type}->{$port}
                  ->{'status'} = 0;
                $device_href->{$dnsname}->{'ports'}->{$assistant_type}->{$port}
                  ->{'pop_state'} = "DISABLED";
                $device_href->{$dnsname}->{'ports'}->{$assistant_type}->{$port}
                  ->{'comment'} = $comment;

                # add to the administrator email message if ecut ports are
                # not found on device
                $message .= "$dnsname,$resource_type,[$port]\n";
                $device_stats++;
            }
        }
    }

    #
    # CASE 3:  there are Device ports missing from ECUT.
    #
    # Don't post to ECUT, instead, just send a message to
    # the ECUT admin.
    #

    foreach my $assistant_type (@assistant_types) {
        foreach $port (@device_port_array) {

            # NOTE: @device_port_array vs @pop_port_array

            # add email entry if a port is not in ecut
            if ( !grep( /^$port$/, @pop_port_array ) ) {

                my ( $chassis, $slot, $port_num ) = split( /\./, $port );
                my $card = "$chassis.$slot";

                # get the linecard metadata
                my $numports =
                  $device_href->{$dnsname}->{'linecards'}->{$assistant_type}
                  ->{$card}->{'num_ports'};
                chomp $numports if $numports;

                my $ltype =
                  $device_href->{$dnsname}->{'linecards'}->{$assistant_type}
                  ->{$card}->{'linecard_type'};
                chomp $ltype if $ltype;

                my $snum =
                  $device_href->{$dnsname}->{'linecards'}->{$assistant_type}
                  ->{$card}->{'serial_number'};
                chomp $snum if $snum;

                my $metadata = "";
                if ($snum) {    # add linecard metadata if available
                    $metadata = "$ltype,$snum,$numports";
                }

                $message .= "$dnsname,$resource_type,,[$port],$metadata\n";
                $import_message .=
"$dnsname-$port,$port,$dnsname,$resource_type,$site,$stakeholder\n";
                $pop_stats++;
            }
        }
    }

    my $stat = poparazzi_mail_log_to_file_attachment( $args_href, $message );
    $stat =
      poparazzi_mail_log_to_import_file_attachment( $args_href,
        $import_message );
    $message  = undef;
    $metadata = undef;

    #
    # CASE 4:  a port is known to ecut and is in the
    # device port list, so just prepare to post it to ECUT.
    #

    foreach my $assistant_type (@assistant_types) {
        foreach $port (@pop_port_array) {    # scan the ecut ports

            if ( grep( /^$port$/, @device_port_array ) ) {

                my $status =
                  $device_href->{$dnsname}->{'ports'}->{$assistant_type}
                  ->{$port}->{'status'};
                my $pop_state =
                  $device_href->{$dnsname}->{'ports'}->{$assistant_type}
                  ->{$port}->{'pop_state'};
                my $comment =
                  $device_href->{$dnsname}->{'ports'}->{$assistant_type}
                  ->{$port}->{'comment'};
            }
        }
    }

    # returning $dnsname totals for missing ecut and device ports
    trace_exit($sub);
    return ( $device_href, $pop_stats, $device_stats );
}

#-------------------------------------------------------------------------------

=head3 tgen_process_utilization_logs($$$$$;)

    This routine processes mulitple utilization logs, returned from
    one host controllers and builds the $device_href DS.  

    Returns: a reference to $device_href

            status
            poparazzi_state
            comment

        for each port in each host controller status log

    Usage:

        $href = tgen_process_utilization_logs
                   ( $args_href, $dnsname, $log_filenames_aref, $device_href );

=cut

#-------------------------------------------------------------------------------

sub tgen_process_utilization_logs ($$$$$;) {

    my $sub = ( caller(0) )[3];
    trace_enter($sub);

    my $args_href      = shift;
    my $dnsname        = shift;
    my $log_names_aref = shift;
    my $logs_aref      = shift;
    my $device_href    = shift;

    my @log_names     = @$log_names_aref;                # casts
    my @logs          = @$logs_aref;
    my $i             = 0;
    my $collector_ini = $args_href->{'collector_ini'};

    # A little tricky: declaring an array to dynamically record
    # the assistant types: either n2x, ixia or both n2x and ixia.
    # Getting the contents of this array from parsing csv files
    my @assistant_array;
    $device_href->{$dnsname}->{'assistant_types_aref'} = \@assistant_array;

    #
    # Design Notes:
    #
    # code will go through the list of log filenames for $dnsname
    # and process the three port status data-points into a hash
    # which is returned in $device_href (passed in for each
    # iteration).
    #
    # for example:
    #
    #  $device_href->{$dnsname}->{'ports'}->{$assistant_type}
    #    ->{$port}->{'status'}     = $status;
    #  $device_href->{$dnsname}->{'ports'}->{$assistant_type}
    #    ->{$port}->{'comment'}    = $comment;
    #  $device_href->{$dnsname}->{'ports'}->{$assistant_type}
    #    ->{$port}->{'pop_state'} = $pop_state;
    #  $device_href->{$dnsname}->{'ports'}->{$assistant_type}
    #    ->{$port}->{'assistant_type'} = n2x or ixia
    #
    # The returned $device_href is used to update ECUT with the status
    # of each port. ECUT tracks ports not dnsnames - the dnsname  is
    # embedded in the port name ($port)
    #

    my $resource_type;

    foreach my $filename (@log_names) {

        # not a part of the time period, only partially finished
        next if $filename =~ /partial/;

        #
        # get the csv for $filename and parse it into an href
        # basiclly, turns a "key,value" string into a $key->{$value} hash
        #

        my $csv_file_aref = $logs[ $i++ ];  # contents of one csv file from host

        if ( !$csv_file_aref or @$csv_file_aref == 0 ) {

            my $msg = "$sub : NULL csv array is empty for file ($filename).";
            poparazzi_log( "LOG_WARN", $msg );
            print "$msg\n";

            #return $false;
            next;
        }

        $device_href = tgen_parse_csv_file_aref( $args_href, $dnsname,
            $csv_file_aref, $device_href );

        # get the assistant_type for the csv file
        # so its clear what type of ports are being processed
        my ($ctype_str) = grep( /controller_type/, @$csv_file_aref );

        # already error checked in the parse csv routine
        # pull out the assistant_type ('n2x' or 'ixia' )
        # gets added to the hash for each port
        my @array          = split( /,/, $ctype_str );
        my $ctype          = $array[1];
        my $assistant_type = $ctype;

        # consolodate the port status from multiple log files
        # - stores status information in $device_href across
        #   invocations and uses that info to determine the
        #   overall status for the port.

        my $href = $device_href->{$dnsname}->{'ports'}->{$assistant_type};

        foreach my $port ( keys %$href ) {

            # current known status
            my $port_href =
              $device_href->{$dnsname}->{'ports'}->{$assistant_type}->{$port};
            my $port_status = $port_href->{'status'};

            # get attributes from the line cards to put into the port hash

            my @parts = split( /\./, $port );
            my $cur_lc = "$parts[0].$parts[1]";

            my $card_model =
              $device_href->{$dnsname}->{'linecards'}->{$assistant_type}
              ->{$cur_lc}->{'linecard_type'};

            my $port_type =
              $device_href->{$dnsname}->{'linecards'}->{$assistant_type}
              ->{$cur_lc}->{'port_type'};
            $port_type = 'undef' if !$port_type && !$card_model;
            $port_type = "missing from '.ini' file"
              if !$port_type && $card_model;
            $card_model = 'undef' if !$card_model;

            my $card_snum =
              $device_href->{$dnsname}->{'linecards'}->{$assistant_type}
              ->{$cur_lc}->{'serial_number'};
            $card_snum = 'undef' if !$card_snum;

            # $status: 1 if used 0 if not
            # $pop_state: as you would assume
            # $comment:  the state from the device (n2x)to be posted
            # subroutine should be device indenpendent

            my $check_aref =
              $device_href->{$dnsname}->{'ports'}->{$assistant_type}->{$port}
              ->{'check_aref'};

            # this sub is used during the csv parse -
            my ( $pop_state, $status, $comment ) =
              tgen_summarize_port_state( $args_href, $assistant_type,
                $check_aref );

            # if a port has been set to USED once, ignore other states
            my $cur_state =
              $device_href->{$dnsname}->{'ports'}->{$assistant_type}->{$port}
              ->{'pop_state'};

            next if $cur_state and $cur_state eq 'USED';

            $device_href->{$dnsname}->{'ports'}->{$assistant_type}->{$port}
              ->{'pop_state'} = $pop_state;
            $device_href->{$dnsname}->{'ports'}->{$assistant_type}->{$port}
              ->{'status'} = $status;
            $device_href->{$dnsname}->{'ports'}->{$assistant_type}->{$port}
              ->{'comment'} = "$comment - Port Type: $port_type";

            $device_href->{$dnsname}->{'ports'}->{$assistant_type}->{$port}
              ->{'port_type'} = $port_type;
            $device_href->{$dnsname}->{'ports'}->{$assistant_type}->{$port}
              ->{'card_model'} = $card_model;
            $device_href->{$dnsname}->{'ports'}->{$assistant_type}->{$port}
              ->{'card_snum'} = $card_snum;
        }
    }

    trace_exit($sub);
    return $device_href;
}

#-------------------------------------------------------------------------------

=head3  tgen_send_cmd_to_host($$$;)

    Send a command to the N2X host controller box ecut Windows service.
    Returns the text returned from the remote host server as an array reference

    Usage:

        my $resuts_aref = tgen_send_cmd_to_host( $args_href, $hostname, $command );


=cut

#-------------------------------------------------------------------------------

sub tgen_send_cmd_to_host($$$;) {

    my $sub = ( caller(0) )[3];
    trace_enter($sub);

    my $args_href = shift;
    my $hostname  = shift;
    my $command   = shift;

    my @ret_array;

    my $telnet_obj = tgen_open_controller_connection( $args_href, $hostname );
    return $false if $telnet_obj == $false;

    my @array = $telnet_obj->cmd($command);

    # cleanup input
    foreach my $elem (@array) {
        next if !$elem;
        chomp $elem;
        next if $elem eq "";
        push( @ret_array, $elem );
    }

    tgen_close_telnet_obj( $args_href, $telnet_obj );

    trace_exit($sub);
    return \@ret_array;
}

# -----------------------------------------------------------------------------------------------------

=head3 tgen_slurp_text($$$;)

    Function    : tgen_slurp_text()
    Description : Convert the csv text string into an array of "lines"
    Parameters  : a csv text string 
    return      : tbd
    Usage       : tgen_slurp_text($args_href, $_text_string, $suffix );
    Keywords    : tgen


    Notes:

        This may be better made a part of the previous slurp routine.

=cut

# -----------------------------------------------------------------------------------------------------

sub tgen_slurp_text ($$$;) {

    my $sub = ( caller(0) )[3];
    trace_enter($sub);

    my $args_href   = shift;
    my $text_string = shift;
    my $suffix      = shift;

    # reusable working variables
    my ( $href, %hash, $aref, $string, $msg );

    my @contents = split( /\/n/, $text_string );

    my $sep;    # the key value seperator
    if ( $suffix eq 'ini' ) {
        $sep = '=';
    }
    if ( $suffix eq 'csv' ) {
        $sep = ',';
    }
    if ( $suffix eq 'txt' ) {
        $sep = "none";
    }

    my ( $ret_href, @ret_array );

    # parse the file into key/value pairs and build
    # the return hash and array

    foreach my $line (@contents) {

        next if !$line;    # line can't be empty
        chomp $line;

        next if $line eq "";       # line can't be blank
        next if $line =~ /^\#/;    # line can't start with a #

        if ( $sep ne 'none' ) {    # line needs a separator if not txt
            next if $line !~ /$sep/;
        }

        my ( $key, $value );

        if ( $suffix eq "txt" ) {    # txt string has a single entry per line

            if ( !$line ) {
                $msg = "malformed line ($line) in text ";
                poparazzi_log( "LOG_ERR", $msg );
                print "ERROR $sub : $msg\n";
                trace_exit($sub);
                return $false;
            }

            push( @ret_array, $line );

        }
        else {    # other formats have one key and value per line

            ( $key, $value ) = split /$sep/, $line;

            if ( !$key or !$value ) {
                $msg = "malformed line ($line) in $suffix text";
                poparazzi_log( "LOG_ERR", $msg );
                print "ERROR $sub : $msg\n";
                trace_exit($sub);
                return $false;
            }

            chomp $key;
            chomp $value;

            push( @ret_array, $key );    # ordered list of keys
            $ret_href->{$key} = $value;  # hash of k/v pairs
        }
    }

    trace_exit($sub);

    return ( $ret_href, \@ret_array );

    #return ( \@string_contents );
}

#-------------------------------------------------------------------------------

=head3 tgen_summarize_port_state($$$;)

    This subaroutine examines the raw string in the $port argument
    and translates that to an ECUT state based on the resource_type.

    Usage:

        my ( $pop_state, $status, $comment ) = 
            tgen_summarize_port_state ( $args_href, $assistant_type, $check_href );

=cut

#-------------------------------------------------------------------------------

sub tgen_summarize_port_state ( $$$;) {

    my $sub = ( caller(0) )[3];
    trace_enter($sub);

    my $args_href      = shift;
    my $assistant_type = shift;
    my $check_aref     = shift;

    # contains the comment field returned from
    # ecutcollector service eg: (port, status, comment)
    my @checks = @$check_aref;

    my ( $pop_state, $status, $comment );

    # available ECUT states for N2X
    # "UNUSED"
    # "USED"
    # "TIMED_OUT"
    # "UNREACHABLE"
    # "INVALID_DEVICE_TYPE"
    # "AUTHENTICATION_FAILED",
    # "UNUSED-REACHED_ROUTER_UPTIME"
    # "USED-ROUTER_UPTIME_FLAG"
    # "UNKNOWN"

    # translate @checks to an ECUT state based on device type

    # defaults
    $status    = 0;
    $pop_state = "UNUSED";
    $comment   = $checks[$#checks];

    if ( $assistant_type eq 'n2x' ) {

        my ($running)   = grep( /RUN/,       @checks );    # returns 1st match
        my ($pending)   = grep( /PENDING/,   @checks );
        my ($capturing) = grep( /CAPTURING/, @checks );

        if ( $running or $pending or $capturing ) {

            $comment = $capturing if $capturing;
            $comment = $pending   if $pending;
            $comment = $running   if $running;

            $status    = 1;
            $pop_state = "USED";
        }
    }
    elsif ( $assistant_type eq 'ixia' ) {

        # test that Total entries are not 0
        # comments strings look like this:
        # 'Frames Sent: 0  Frames Recv: 0',
        # or each may have a value

        my $test1 = "Frames Sent: ";
        my $test2 = "Frames Recv: ";

        # set in $ECUT_ROOT/etc/poparazzi.ini
        my $threshold = $args_href->{minimum_traffic_threshold};
        my ( $send_total, $recv_total );

        foreach my $str (@checks) {
            chomp $str;

            # identify strings with traffic data
            if ( $str =~ /$test1/ or $str =~ /$test2/ ) {

                # get the totals
                my @array = split( / /, $str );
                my $s_total =
                  $array[2];    # this is just where they end up in the array
                my $r_total = $array[6];

                # get absolute value
                $s_total = $s_total * -1 if $s_total < 0;
                $r_total = $r_total * -1 if $r_total < 0;

                # set utilization
                if ( $s_total > $threshold or $r_total > $threshold ) {
                    $pop_state = 'USED';
                    $comment   = $str;
                    $status    = 1;
                }
                else {
                    $pop_state = 'UNUSED';
                    $comment   = $str;
                    $status    = 0;
                }
            }
        }
    }
    else {
        # should never happen
        print "FATAL $sub : Programming error: unknown type: $assistant_type\n";
        exit;
    }

    trace_exit($sub);
    return ( $pop_state, $status, $comment );
}

#-------------------------------------------------------------------------------

=head3 tgen_translate_port_to_csp_format ( $; );

    returns a port in csp format.

    Usage:

        my $port = tgen_translate_port_to_csp_format ( $port );


=cut

#-------------------------------------------------------------------------------

sub tgen_translate_port_to_csp_format ($;) {

    my $sub = ( caller(0) )[3];
    trace_enter($sub);

    my $port = shift;

    my @port_array = split( /\./, $port );
    my $a_size = @port_array;    # based on dots in string

    # $port already in csp format
    if ( $a_size == 3 ) {
        trace_exit($sub);
        return $port;
    }

    if ( $a_size != 2 ) {
        print "FATAL $sub: don't know how to translate port name ($port)\n";
        retrun $port;
    }

    my $cs_part   = $port_array[0];
    my $port_part = $port_array[1];

    my @slot_array = split( //, $cs_part );
    my $s_size = @slot_array;    # based on numbrers in string

    my $zero  = $slot_array[0];
    my $one   = $slot_array[1];
    my $two   = $slot_array[2];
    my $three = $slot_array[3] if $s_size == 4;

    my ( $ret_str, $chassis, $slot );

    if ( $s_size == 4 ) {    # 4111.1
        $chassis = $zero . $one;          # dot joins
        $slot    = $two . $three;
        $slot    = $three if $two == 0;
    }
    else {                                # 201.1
        $chassis = $zero;
        $slot    = $one . $two;
        $slot    = $two if $one == 0;
    }

    $ret_str = "$chassis.$slot.$port_part";

    trace_exit($sub);
    return $ret_str;
}

#-------------------------------------------------------------------------------

=head3 tgen_update_pop_port_status($$$;)

    This routine updates the ECUT website with the contents
    of $device_href, which contains the data for each
    port/resource for the $dnsname argument.

    Returns:  $true on success $false on failure.

    Usage:

        $status = tgen_update_pop_port_status ($args_href, $dnsname, $device_href );

=cut

#-------------------------------------------------------------------------------

sub tgen_update_pop_port_status ($$$;) {

    my $sub = ( caller(0) )[3];
    trace_enter($sub);

    my $args_href   = shift;
    my $dnsname     = shift;
    my $device_href = shift;    # ports from device/$dnsname

    # collapse the device_href - removes $assistant_type and captures
    # the 'USED' ports.  'UNUSED' port information will be valid but
    # can come from any $assistant_type port.

    # NOTE: don't return this collapsed $device_href, there are differences
    # the collapsed hash is the data that is posted to ecut
    $device_href = tgen_collapse_device_href( $args_href, $device_href );

    #
    #   Return on audit and xml flags
    #
    #  The audit and xml flags don't post to ecut
    #
    return if $args_href->{'audit_arg'} || $args_href->{'xml_arg'};

    #
    # Update to ECUT
    #

    my $timestamp     = $args_href->{'timestamp'};
    my $resource_type = $args_href->{'resource_type'};

    #
    # Pull out the array of ecut ports for the current dnsname.
    # Ports known to ECUT can differ from host ports.  These
    # differences are documented in the administrator's email.
    #

    my $pop_href = $args_href->{'pop_href'};
    my $port;

    my $aref           = $pop_href->{$dnsname}->{'pop_port_aref'};
    my @pop_port_array = sort @$aref;

    #
    # ECUT Update Driver block
    #

    foreach my $port (@pop_port_array) {

        my $port_href = $device_href->{$dnsname}->{'ports'}->{$port};
        my $status    = $port_href->{'comment'};
        my $pop_state = $port_href->{'pop_state'};
        my $comment   = $port_href->{'comment'};

        my $port_type  = $port_href->{'port_type'};
        my $card_model = $port_href->{'card_model'};
        my $card_snum  = $port_href->{'card_snum'};

        my $port_entry_name = "$dnsname-$port";

        # debug
        #ref_dump ( $port_href );
        #exit;

        # values for the undefined
        $port_type  = "" if !$port_type;
        $card_model = "" if !$card_model;
        $card_snum  = "" if !$card_snum;

        my $resource_name = "$dnsname-$port";

        # update utilization data to the ECUT webserver
        my $update =
          poparazzi_update_port_utilization_entry( $args_href, $resource_type,
            $dnsname, $port, $timestamp, $pop_state, $comment );

        # update properties to the ECUT webservice  - used in other tools
        $update = poparazzi_post_property_value_by_resource_name( $args_href,
            $resource_name, 'porttype', $port_type );
        $update = poparazzi_post_property_value_by_resource_name( $args_href,
            $resource_name, 'cardModel', $card_model );
        $update =
          poparazzi_post_property_value_by_resource_name( $args_href,
            $resource_name, 'cardSerialNumber', $card_snum );
    }

    trace_exit($sub);
    return $true;
}

#-----------------------------------------------------------------------------------------------------

=head3 poparazzi_create_new_project ($;)

    Desc:       create a sparse application file and a program module from templates

    Parameters : $args_href, $module_name
    Return     : $true or $false

    Usage:

        my $status = poparazzi_create_new_project ( $args_href, $module_name );

=cut

#-----------------------------------------------------------------------------------------------------

sub poparazzi_create_new_project ($;) {

    my $sub = ( caller(0) )[3];
    trace_enter($sub);

    my $args_href = shift;

    # reusable variable names
    my ( $dialog_href, $msg, $response, $str, $status, $default, @array );

    # the gathered data variables
    my ( $app_name, $pkg_list, $author, $organization, $stub_count,
        $stub_list );

    my $intro = $args_href->{'intro_to_new_project'};
    $msg     = "Do you want to create POP project files at this time (y\/n)?";
    $default = "n";

    $response = poparazzi_dialog_start( $intro, $msg, $default );
    return $false if $response eq "n" or $response eq "no";

    $msg      = "Enter the Application name";
    $default  = $args_href->{'defaults'}->{'app_name'};
    $response = poparazzi_dialog_continue( $msg, $default );

    while ( !$response or $response eq "" ) {

        $msg      = "You need to enter a name string. (CTRL-C to exit)";
        $response = poparazzi_dialog_continue($msg);
    }

    # verify $app_name
    # other names are built from $app_name
    $app_name = $response;
    if ( grep /\.pl$/, $app_name or grep /\.pm$/, $app_name ) {
        my @parts = split( /\./, $app_name );
        $app_name = $parts[0];
    }
    $app_name = lc $app_name;

    # build the other names
    my $app_filename  = "$app_name.pl";
    my $mod_name      = ucfirst($app_name);
    my $mod_filename  = "$mod_name.pm";
    my $prep_filename = "prep_" . $app_name . ".sh";

    # save the names in dialog_href
    $dialog_href->{'app_name'}      = $app_name;
    $dialog_href->{'mod_name'}      = $mod_name;
    $dialog_href->{'app_filename'}  = $app_filename;
    $dialog_href->{'mod_filename'}  = $mod_filename;
    $dialog_href->{'prep_filename'} = $prep_filename;

    $msg          = "Name of the Organization";
    $default      = $args_href->{'defaults'}->{'organization'};
    $response     = poparazzi_dialog_continue( $msg, $default );
    $organization = $response;
    $dialog_href->{'organization'} = $response;

    $msg                     = "Author's Name";
    $default                 = $args_href->{'defaults'}->{'author'};
    $response                = poparazzi_dialog_continue( $msg, $default );
    $author                  = $response;
    $dialog_href->{'author'} = $response;

    #
    #    print out the gathered data and get user buy-in
    #

    print "\n";
    print "    Here are the values you have entered:";
    print "\n";
    print "        Application name:  $dialog_href->{'app_name'}\n";
    print "        Organization name: $dialog_href->{'organization'}\n";
    print "        Author name:       $dialog_href->{'author'}\n";
    print "\n";

    $msg =
      "Do you want to create project files using these values (yes or no )?";
    $response = poparazzi_dialog_continue($msg);

    while ( $response ne 'yes' and $response ne 'no' ) {

        $msg      = "You need to enter yes or no";
        $response = poparazzi_dialog_continue($msg);
    }

    if ( $response eq 'no' ) {
        trace_exit($sub);
        return $false;
    }

    # save the default values to the config file
    # for future calls to the tool
    my $config_filename = $args_href->{'poparazzi_config_filename'};
    my $config_fh       = pop_create_w_filehandle($config_filename);

    foreach my $key ( keys %$dialog_href ) {
        my $val = $dialog_href->{$key};
        print $config_fh "$key,$val\n";
    }
    close($config_fh);

    # time to make the files from templates defined in init_common_data

    $status =
      poparazzi_create_sparse_application_file( $args_href, $dialog_href );

    $status = poparazzi_create_pop_module_file( $args_href, $dialog_href );

    $status = poparazzi_create_pop_prep_file( $args_href, $dialog_href );

    pop_shell("chmod 744 $app_filename");
    pop_shell("chmod 744 $mod_filename");
    pop_shell("chmod 744 $prep_filename");

    trace_exit($sub);
    return $true;
}

# fixglobals
sub poparazzi_move_globals_to_args_href ( $; ) {
    my $sub = ( caller(0) )[3];
    trace_enter($sub);
    my $args_href = shift;
    print "move 1\n";
    trace_exit($sub);
    return $true;
}

# orderlib
sub poparazzi_alphabitize_library ( $; ) {
    my $sub = ( caller(0) )[3];
    trace_enter($sub);
    my $args_href = shift;
    print "alpha\n";
    trace_exit($sub);
    return $true;
}

# movetolib
sub poparazzi_move_subs_to_lib ( $; ) {
    my $sub = ( caller(0) )[3];
    trace_enter($sub);
    my $args_href = shift;
    print "move 2\n";
    trace_exit($sub);
    return $true;
}

# checkpod
sub poparazzi_check_pod_headers ( $; ) {

    my $sub = ( caller(0) )[3];
    trace_enter($sub);

    my $args_href = shift;

    print "check\n";
    trace_exit($sub);
    return $true;
}

#-----------------------------------------------------------------------------------------------------

=head3 poparazzi_write_new_subroutine_block ( $$$; )

    Desc:        prints a new subroutine block to a file handle

    Parameters :  $file_handle, $app_name, $sub_name
    Return     : 

    Usage:

       

=cut

#-----------------------------------------------------------------------------------------------------

sub poparazzi_write_new_subroutine_block ($$$;) {

    my $sub = ( caller(0) )[3];
    trace_enter($sub);

    my $file_handle = shift;
    my $app_name    = shift;
    my $sub_name    = shift;

    print $file_handle
"#-------------------------------------------------------------------------------\n";
    print $file_handle "\n";
    print $file_handle "=head3  " . $sub_name . "(\$;)\n";
    print $file_handle "\n";
    print $file_handle "    Desc:  TODO\n";
    print $file_handle "\n";
    print $file_handle "    Usage:\n";
    print $file_handle "\n";
    print $file_handle "        my \$status = "
      . $sub_name
      . " ( \$args_href );\n";
    print $file_handle "\n";
    print $file_handle "\n";
    print $file_handle "=cut\n";
    print $file_handle "\n";
    print $file_handle
"#-------------------------------------------------------------------------------\n";
    print $file_handle "\n";
    print $file_handle "sub " . $sub_name . "(\$;) {\n";
    print $file_handle "\n";
    print $file_handle "    my \$sub = ( caller(0) )[3];\n";
    print $file_handle "    trace_enter(\$sub);\n";
    print $file_handle "\n";
    print $file_handle "    my \$args_href = shift;\n";
    print $file_handle "\n";
    print $file_handle "    # ///\n";
    print $file_handle "\n";
    print $file_handle "    # do stuff\n";
    print $file_handle "\n";
    print $file_handle "    # ///\n";
    print $file_handle "    print\n";
    print $file_handle
"\"\n    ERROR in \$sub: You have invoked an unaltered stub subroutine. Exiting...\\n\\n\\n\";\n";
    print $file_handle "    exit 0;\n";
    print $file_handle "\n";
    print $file_handle "    trace_exit(\$sub);\n";
    print $file_handle "    return \$true;\n";
    print $file_handle "}\n";
    print $file_handle "\n";

    trace_exit($sub);
    return $true;
}

#-------------------------------------------------------------------------------

=head1 ^

=cut

1;    # always the last statement in any Perl module file

#-------------------------------------------------------------------------------

