#-------------------------------------------------------------------------------

=head1 POP.pm

=cut

=head1 Synopsis

    A POP Module  - collection of possibly useful POP stuff.

    Usage:

        use POP;

=cut

#-------------------------------------------------------------------------------

=head3 File History

    1/1/1970  - MOA  - first implementation of the app.

=cut

#-------------------------------------------------------------------------------

=head3 Module Dependencies

    use strict
    use warnings
    use Data::Dumper

=cut

#-------------------------------------------------------------------------------

# loader section

use strict;
use warnings;
use Data::Dumper;

# the only Globals Please

my $true  = ( 1 == 1 );
my $false = !$true;

#-------------------------------------------------------------------------------

=head1 Subroutines

=cut

#-------------------------------------------------------------------------------

=head3  trace_enter($;)

    This subroutine checks if trace is set and prints trace info.

    Usage:

        my $sub = ( caller(0) )[3];
        trace_enter( $sub );

=cut

#-------------------------------------------------------------------------------

sub trace_enter($;) {

    my $sub = shift;

    print "TRACE: entering $sub\n" if $ENV{POP_TRACE};

    return;
}

#-------------------------------------------------------------------------------

=head3  trace_exit($;)

    This subroutine checks if trace is set and prints trace info.

    Usage:

        trace_exit ( $sub );

=cut

#-------------------------------------------------------------------------------

sub trace_exit($;) {

    my $sub = shift;

    print "TRACE: exiting $sub\n" if $ENV{POP_TRACE};

    return;
}

#-------------------------------------------------------------------------------

=head3 pop_backticks($;)

    Wrapper for backticks - captures status and shell output.

    Arguments:

        $cmd - the command to run

    Returns:

        $true or $false

    Usage:

        my ($output, $status) = pop_backticks( $cmd );

        my $status            = pop_backticks( $cmd );

=cut

#-------------------------------------------------------------------------------

sub pop_backticks ($;) {

    my $sub = ( caller(0) )[3];
    trace_enter($sub);

    my $cmd = shift;

    my @output = `$cmd`;

    if ($?) {
        my $msg = "Failed to execute '$cmd' on the local host: $?";
        print "$msg\n";    # can be logged

        trace_exit($sub);
        return \@output, $false;
    }

    # can be logged
    #my $msg = "$sub: '$cmd' succeeded on local host\n";

    trace_exit($sub);
    return \@output, $true;
}

#-------------------------------------------------------------------------------

=head3  pop_create_filehandle($$;)

    Create a filehandle with mode argument, without "or die"

    Args:  filename and mode ( < | > | +> | >> | etc... )
    
    Usage:

        my $fh = pop_create_filehandle( $filename, $mode );

=cut

#-------------------------------------------------------------------------------

sub pop_create_filehandle ($$;) {

    my $sub = ( caller(0) )[3];
    trace_enter($sub);

    my $filename = shift;
    my $mode     = shift;

    my ($msg);

    if ( !$filename or $filename eq "" ) {
        print "ERROR $sub: missing $filename\n";
        trace_exit($sub);
        exit $false;
    }

    if ( !$mode or $mode eq "" ) {
        print "ERROR $sub: missing mode argument\n";
        trace_exit($sub);
        exit $false;
    }

    my $filehandle;

    my $rc = open $filehandle, "$mode", $filename;
    if ( !defined $rc ) {

        print "FATAL $sub: $mode open on $filename failed\n";
        print "FATAL $sub: open returned \"$!\"\n";
        trace_exit($sub);
        exit 0;
    }

    trace_exit($sub);
    return $filehandle;
}

#-------------------------------------------------------------------------------

=head3  pop_create_r_filehandle($;)

    Open a file for reading and return the filehandle without "or die"
    
    Usage:

        my $fh = pop_create_r_filehandle( $filename );

        my @file_contents_array  = <$fh>;

=cut

#-------------------------------------------------------------------------------

sub pop_create_r_filehandle ($;) {

    my $sub = ( caller(0) )[3];
    trace_enter($sub);

    my $filename = shift;
    my $mode     = '<';

    my $filehandle = pop_create_filehandle( $filename, $mode );

    trace_exit($sub);
    return $filehandle;
}

#-------------------------------------------------------------------------------

=head3  pop_create_w_filehandle($;)

    Open a file for write and return the filehandle without "or die"
    
    Usage:

        my $fh = pop_create_w_filehandle( $filename );

        print $fh "message\n";

=cut

#-------------------------------------------------------------------------------

sub pop_create_w_filehandle ($;) {

    my $sub = ( caller(0) )[3];
    trace_enter($sub);

    my $filename = shift;
    my $mode     = '>';

    my $filehandle = pop_create_filehandle( $filename, $mode );

    trace_exit($sub);
    return $filehandle;
}

#---------------------------------------

=head3 pop_shell($;)

    Arguments: $command
    Returns: success: 0
             failure: 1

    Run a command using backticks and return
    $true  on success and $false  on error.

=cut

#---------------------------------------
sub pop_shell($;) {

    my $sub = ( caller(0) )[3];
    trace_enter($sub);

    my $cmd = shift;

    if ( !$cmd ) {
        my $msg = "Missing argument to $sub";
        print "FATAL $sub: $msg\n";
        exit 0;
    }

    my $trace = $ENV{ECUT_TRACE};

    if ( defined $trace && $trace == 1 ) {
        print " - ";
    }

    my $rc = `$cmd`;

    my $status = $? >> 8;

    if ( $? != 0 ) {

        my $msg = "Execution of $cmd failed.";

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

=head3 pop_shell_remote($$$;$)

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

sub pop_shell_remote($$$;$) {

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
        $msg .= "Note logging from pop_shell_remote";

        #pop_log( "LOG_WARN", $msg );

        trace_exit($sub);
        return ( $false, $rc );
    }

    trace_exit($sub);
    return ( $true, $rc );
}

#-------------------------------------------------------------------------------

=head3  pop_slurp_file_into_aref($;)

    Read ether a file into an array and return its reference
    
    filename should be the full path to the file

    Usage:

        my $aref = pop_slurp_file_into_aref ( "filename.ini" );

    Notes:

        Returns $false if the filename doesn't exist

=cut

#-------------------------------------------------------------------------------

sub pop_slurp_file_into_aref ($;) {

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

    #
    my $fh            = pop_create_r_filehandle($filename); # opens file
    my @file_contents = <$fh>;                              # read into an array
    close($fh);

    if ( !@file_contents or @file_contents eq $false ) {

        $msg = "Slurping '$filename' returned empty or undefined file contents";
        print "WARNING $sub : $msg\n";
        trace_exit($sub);
        return $false;
    }

    trace_exit($sub);
    return \@file_contents;
}

#-------------------------------------------------------------------------------

=head3  pop_slurp_file_into_string($;)

    Returns a string of the file contents
    
    Filename argument should be the full path to the file

    Usage:

        my $string  = pop_slurp_file_into_string ( "filename.ini" );

    Notes:

        Returns $false if the filename doesn't exist

=cut

#-------------------------------------------------------------------------------

sub pop_slurp_file_into_string ($;) {

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

    #
    my $fh            = pop_create_r_filehandle($filename); # opens file
    my $file_contents = <$fh>;                              # read into a string
    close($fh);

    if ( !$file_contents or $file_contents eq $false ) {

        $msg = "Slurping '$filename' returned empty or undefined file contents";
        print "WARNING $sub : $msg\n";
        trace_exit($sub);
        return $false;
    }

    trace_exit($sub);
    return $file_contents;
}

#-------------------------------------------------------------------------------

=head3  pop_slurp_file_with_suffix($;)

    Read ether an 'ini', a 'csv' file or a 'txt' file and return a hash
    reference to the file contents and an array of ordered keys
    
    filename should be the full path to the file

    Usage:

        my ( $href, $aref )  = pop_slurp_file_with_suffix ( "filename.ini" );
        my ( $href, $aref )  = pop_slurp_file_with_suffix ( "filename.csv" );
        my $aref             = pop_slurp_file_with_suffix ( "filename.txt" );

    Notes:

        In the case of a text file, each line in the file 
        is added to an array which is returned as a reference.
        The hash reference is not returned, since a txt file is
        not composed of key value pairs, in the case of the other
        file sffixs' the hash has the k/v pairs and the array
        holds the ordered list of keys.

=cut

#-------------------------------------------------------------------------------

sub pop_slurp_file_with_suffix ($;) {

    my $sub = ( caller(0) )[3];
    trace_enter($sub);

    my $filename = shift;

    # reusable working variables
    my ( $href, %hash, $aref, $string, $msg );

    # get file contents
    $aref = pop_slurp_file_into_aref($filename);
    return $false if $aref eq $false;

    my @file_contents = @$aref;

    # parse the file suffix
    my @parts = split( /\./, $filename );
    my $suffix = $parts[$#parts];
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

                #pop_log( "LOG_ERR", $msg );
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

                #pop_log( "LOG_ERR", $msg );
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

#-------------------------------------------------------------------------------

=head3 pop_system($;)

    Wrapper for system - captures status and shell output.

    Arguments:

        $cmd - the command to run as a single string.
               the cmd string can contain any number of arguments - for example:

               my $cmd = "find . -type f -exec grep "hello" {} \; -print";

    Returns:

        $false if the command failed
        or the value returned from the shell

    Usage:

        my $status  = pop_system( $cmd );

=cut

#-------------------------------------------------------------------------------

sub pop_system ($;) {

    my $sub = ( caller(0) )[3];
    trace_enter($sub);

    my $cmd = shift;

    if ( $? == -1 ) {    # command failed
        trace_exit($sub);
        return $false;
    }

    trace_exit($sub);
    return $? >> 8;      # return rc from the shell
}

#-------------------------------------------------------------------------------

=head3  ref_dump($;)

    This subroutine wraps Data::Dumper.  Just pass in a data structure,
    it dumps it out. This is KISS thing, makes it simple...

    This is used for debugging data structures during development.

    Usage:

        ref_dump ( $data_structure );

    No Reutrn

=cut

#-------------------------------------------------------------------------------

sub ref_dump ($;) {

    my $sub = ( caller(0) )[3];
    trace_enter($sub);

    my $data_structure = shift;

    print "WARNING $sub: Missing or undefined data structure argument\n"
      if !defined $data_structure;

    #print "$sub: Dumping datastructure \n";
    print Dumper ($data_structure) . "\n";

    #print "$sub: done\n";

    trace_exit($sub);
    return;
}

#-------------------------------------------------------------------------------

=head1 ^

=cut

1;    # EOF
