# *** READEME ***
# cd to C_file folder before running this script
# set c_file_name <name of C file to compile>

# compile and link library (2-steps)
exec xsc ../C_files/$c_file_name -gcc_compile_options "-I/usr/local/include/opencv4 -L/usr/local/lib -g -lopencv_core -lopencv_imgproc -lopencv_highgui -lstdc++ -lopencv_imgcodecs"

# get current active simset
set active_sim_set [current_fileset -simset]

# copy shared lib from compile dir to current simset xsim.dir
## 1. get the destination path
set dest_dir [get_property directory [current_project]]/[current_project].sim/$active_sim_set/behav/xsim/ 

## 2. execute copy
exec cp ./xsim.dir/work/xsc/dpi.so $dest_dir

# xelab config
set_property -name {xsim.elaborate.xelab.more_options} -value {-sv_lib "dpi.so" -L uvm} -objects [get_filesets $active_sim_set]








