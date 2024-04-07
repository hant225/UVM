# Reset Simulation
reset_simulation -simset [current_fileset -simset] -mode behavioral

# Run DPI Script
source ../SCRIPTS/run_dpi_lib_create.tcl

# Launch Simulation
launch_simulation -simset [get_filesets $active_sim_set]
