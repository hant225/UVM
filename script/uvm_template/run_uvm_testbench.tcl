# ********************************************************* READ ME *****************************************************************
# run this before running the script below: set filename <file_name>
# this script create a simulation file in the current active sim set with the file name is the result of [set filename <file_name>] above
# this script also automatically create code for uvm_component class as the skeleton_src below
# to run this script: source path/uvm_comp_create.tcl
# change the skeleton_src below to config the auto-created uvm_component code in file

######################################################################################################################################
############################################################## CREATE SIM FILE IN VIVADO #############################################
######################################################################################################################################


create_fileset -simset $simsetname
current_fileset -simset [ get_filesets $simsetname ]
set simset_dir [get_property directory [current_project]]/[current_project].srcs/${simsetname}/new

## file mkdir /home/hao/Documents/0.KHOA_LUAN_TOT_NGHIEP/uvm_part2/uvm_part2.srcs/sim_temp3/new
file mkdir $simset_dir                        

set filename transaction
source ./Downloads/tcl_test/run_create_transaction.tcl

set filename sequences
source ./Downloads/tcl_test/run_create_sequences.tcl

set filename driver
source ./Downloads/tcl_test/run_create_driver.tcl

set filename monitor
source ./Downloads/tcl_test/run_create_monitor.tcl

set filename scoreboard
source ./Downloads/tcl_test/run_create_scoreboard.tcl

set filename agent
source ./Downloads/tcl_test/run_create_agent.tcl

set filename env
source ./Downloads/tcl_test/run_create_env.tcl

set filename test
source ./Downloads/tcl_test/run_create_test.tcl
update_compile_order -fileset $simsetname

