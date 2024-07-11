`timescale 1ns / 1ps
`include "uvm_macros.svh"
import uvm_pkg::*;

//////////////////////////////////////////////////////////////////////////////////

class convDW_monitor extends conv1_monitor;

    // Register to Factory
    `uvm_component_utils(convDW_monitor)
    
    // Properties   
    convDW_transaction tr;
    virtual convDW_if vif;  
    int valid_count = 0;      
    
    // Analysis Port
    uvm_analysis_port #(convDW_transaction) send;
    
    // Constructor
    function new(input string path = "MON", uvm_component parent = null);
        super.new(path, parent);
    endfunction
    
    // Build Phase
    virtual function void build_phase(uvm_phase phase);
        super.build_phase(phase);
        tr = convDW_transaction::type_id::create("tr");
        if(!uvm_config_db#(virtual convDW_if)::get(this, "", "vif", vif))
            `uvm_error("MON", "UNABLE TO ACCESS THE INTERFACE!!!");
        send = new("send", this);
    endfunction
    
    // Run Phase
    virtual task run_phase(uvm_phase phase);
        super.run_phase(phase);
    endtask
    
endclass