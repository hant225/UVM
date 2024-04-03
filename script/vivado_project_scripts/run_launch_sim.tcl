# Run DPI Script
source ../SCRIPTS/run_dpi_lib_create.tcl

# Launch Simulation
close_sim
launch_simulation -simset [get_filesets $active_sim_set]
