`timescale 1ns / 1ps
`include "uvm_macros.svh"
import uvm_pkg::*;

//////////////////////////////////////////////////////////////////////////////////

class convDW_driver extends conv1_driver;
    // Register to Factory
    `uvm_component_utils(convDW_driver)
    
    // Properties   
    convWD_transaction tr;
    virtual convDW_if vif;
    
    // Constructor
    function new(input string path = "DRV", uvm_component parent = null);
        super.new(path, parent);
    endfunction
    
    // Build Phase
    virtual function void build_phase(uvm_phase phase);
        super.build_phase(phase);
        tr = convDW_transaction::type_id::create("tr");
        if(!uvm_config_db#(virtual convDW_if)::get(this, "", "vif", vif))
            `uvm_error("DRV", "UNABLE TO ACCESS THE INTERFACE!!!")
    endfunction
    
    // Run phase
    virtual task run_phase(uvm_phase phase);
        drive(tr);
    endtask
    
    // Methods
    task drive(conv1_transaction tr);
        super.drive(tr);
    endtask
            
endclass