# UVM

# After creating the vivado project, create 3 new folder inside the project folder:
  +  C_files : store all C files here
  +  runDir  : cd to this dir before running the scripts
  +  SCRIPTS : store all TCL scripts here



# The folder tree looks like below:

vivado_project_dir
│
├── C_files
│   └── hello_world.c
├── runDir
│   ├── xsc.log
│   ├── xsc.pb
│   └── xsim.dir
│       └── work
│           └── xsc
│               ├── dpi.so
│               └── hello_world.lnx64.o
├── SCRIPTS
│   ├── run_dpi_lib_create.tcl
│   └── run_launch_sim.tcl
│
└── Others_vivado_auto_create_folders
