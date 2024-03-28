`timescale 1ns / 1ps
`include "uvm_macros.svh"
import uvm_pkg::*;

//////////////////////////////////////////////////////////////////////////////////

class test extends uvm_test;
    // Register to Factory
    `uvm_component_utils(test)
    
    // Properties
    env e;
    std_seq ss;
    int log_file;
    
    // Constructor
    function new(input string path = "TEST", uvm_component parent = null);
        super.new(path, parent);       
    endfunction
    
    // Build Phase
    virtual function void build_phase(uvm_phase phase);
        super.build_phase(phase);
        e  = env::type_id::create("e", this);
        ss = std_seq::type_id::create("ss");
    endfunction
    
    // Run Phase
    virtual task run_phase(uvm_phase phase);
        log_file = $fopen("/home/hao/Documents/0.KHOA_LUAN_TOT_NGHIEP/log_dir/pe_conv_mac_report.txt");
        uvm_top.set_report_default_file_hier(log_file);
        uvm_top.set_report_severity_action_hier (UVM_INFO, UVM_DISPLAY | UVM_LOG);
        phase.raise_objection(this);
            ss.start(e.a.seqr);
        phase.drop_objection(this);
        
    endtask
endclass

