#!/usr/bin/perl

# Open the log file for reading
open(my $fh, '<', 'pe_conv_mac_report.txt') or die "Could not open file 'logfile.log' $!";

# Open a file handle for writing the output
open(my $output_fh, '>', 'retouched_pe_conv_mac_report.txt') or die "Could not open file 'output.txt' $!";

my $table_stripe = "+---------+-----------------------------------+---------------------------------------------------------------------------------------------------------------------------------+\n";
# PRINT TO SCREEN
printf            ("\n\n");
print             "$table_stripe";
printf            ("|  TIME   |            HIERARCHY              |                                                             MESSAGE                                                             |\n");
print             "$table_stripe";
# WRITE TO FILE
printf $output_fh ("\n\n");
printf $output_fh ("%s", $table_stripe);
printf $output_fh ("|  TIME   |            HIERARCHY              |                                                             MESSAGE                                                             |\n");
printf $output_fh ("%s", $table_stripe);

# Loop through each line in the log file
while (my $line = <$fh>) {
    if($line =~ /@/ && $line =~ /UVM_INFO/) {	
        $line =~ s/^.*?@//; 				# Remove the directory path entirely      
        $line =~ s/^\s+//; 				# Remove the first space in the line

        # Split the log message into three parts based on the first and second space characters
        my ($time_var, $hier_var, $msg_var) = split(/\s+/, $line, 3); 
        $time_var = substr($time_var, 0, -4); 		# remove last 0000 of time
        chomp($msg_var); 				# remove \n character
      
        # PRINT
        printf            ("|   %-5s |    %-30s |    %-125s|\n", $time_var, $hier_var, $msg_var);		# TO SCREEN
        printf $output_fh ("|   %-5s |    %-30s |    %-125s|\n", $time_var, $hier_var, $msg_var);         # TO FILE
    }
    else{
        my $time_var = " ";
        my $hier_var = " ";
        my $msg_var  = " ";
    
        $msg_var = $line;
        chomp($msg_var);
        printf            ("|   %-5s |    %-30s |    %-125s|\n", $time_var, $hier_var, $msg_var);		# TO SCREEN
        printf $output_fh ("|   %-5s |    %-30s |    %-125s|\n", $time_var, $hier_var, $msg_var);		# TO SCREEN
    }
}
# PRINT TO SCREEN
print  "$table_stripe";
printf ("\n\n");
# PRINT TO FILE
printf $output_fh ("%s", $table_stripe);
printf $output_fh ("\n");
printf $output_fh ("$report_sum");
printf $output_fh ("\n\n");

# Close the file handles
close($fh);
close($output_fh);

