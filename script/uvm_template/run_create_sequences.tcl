# ********************************************************* READ ME *****************************************************************
# run this before running the script below: set filename <file_name>
# this script create a simulation file in the current active sim set with the file name is the result of [set filename <file_name>] above
# this script also automatically create code for uvm_component class as the skeleton_src below
# to run this script: source path/uvm_comp_create.tcl
# change the skeleton_src below to config the auto-created uvm_component code in file

######################################################################################################################################
############################################################## CREATE SIM FILE IN VIVADO #############################################
######################################################################################################################################
# get the current sim set
set active_sim_set [current_fileset -simset]
# get the project directory
set project_dir [get_property directory [current_project]]
# get new file directory
set new_file_dir ${project_dir}/[current_project].srcs/${active_sim_set}/new/${filename}.sv

# create file
set_property SOURCE_SET [current_fileset] [get_filesets $active_sim_set]
close [ open $new_file_dir w ]
add_files -fileset $active_sim_set $new_file_dir
#######################################################################################################################################
################################################################ SKELETON SOURCE ######################################################
#######################################################################################################################################
set skeleton_src {`timescale 1ns / 1ps
`include "uvm_macros.svh"
import uvm_pkg::*;

//////////////////////////////////////////////////////////////////////////////////

class sequence1 extends uvm_sequence#(transaction);   
    // Register to Factory
    `uvm_object_utils()
    
    // Properties   
    transaction tr;
    
    // Constructor
    function new(input string path = "valid_din");
        super.new(path);
    endfunction
    
    // Body
    virtual task body();

    endtask
endclass

}

#######################################################################################################################################
################################################## CREATE SKELETON FOR THE CREATED FILE ###############################################
#######################################################################################################################################

set file_id [open $new_file_dir "w"]
puts $file_id $skeleton_src
# create uvm_component with skeleton
close $file_id
#######################################################################################################################################


