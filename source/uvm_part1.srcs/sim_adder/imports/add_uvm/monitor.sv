`timescale 1ns / 1ps
`include "uvm_macros.svh"
import uvm_pkg::*;

//////////////////////////////////////////////////////////////////////////////////

class monitor extends uvm_monitor;
    // Register to Factory
    `uvm_component_utils(monitor)
    
    // Properties
    transaction tc;
    virtual add_if aif;
    uvm_analysis_port #(transaction) send;
    
    // Constructor
    function new(string path = "MON", uvm_component parent = null);
        super.new(path, parent);
        send = new("send", this);
    endfunction
    
    // Build Phase
    virtual function void build_phase(uvm_phase phase);
        super.build_phase(phase);
        tc = transaction::type_id::create("tc");
        if(!uvm_config_db#(virtual add_if)::get(this, "", "aif", aif))
            `uvm_error("MON", "Unable to access interface");
    endfunction
    
    // Run Phase
    virtual task run_phase(uvm_phase phase);
        forever begin
            #10
            `uvm_info("MON", "Waiting for Transaction..", UVM_NONE);
            tc.a = aif.a;
            tc.b = aif.b;
            tc.y = aif.y;
            `uvm_info("DRV", "Transaction received.. Sending to SCB..", UVM_NONE)
            send.write(tc);
        end
    endtask
endclass

//////////////////////////////////////////////////////////////////////////////////

