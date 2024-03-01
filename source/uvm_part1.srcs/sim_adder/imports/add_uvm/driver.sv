`timescale 1ns / 1ps
`include "uvm_macros.svh"
import uvm_pkg::*;

//////////////////////////////////////////////////////////////////////////////////

class driver extends uvm_driver#(transaction);
    // Register to Factory
    `uvm_component_utils(driver)
    
    // Properties
    transaction t;
    virtual add_if aif;
    
    // Constructor
    function new(string path = "DRV", uvm_component parent = null);
        super.new(path, parent);
    endfunction
    
    // Build Phase
    virtual function void build_phase(uvm_phase phase);
        super.build_phase(phase);
        t = transaction::type_id::create("t");
        if(!uvm_config_db#(virtual add_if)::get(this, "", "aif", aif))
            `uvm_error("DRV", "Unable to access interface");
    endfunction
    
    // Run Phase
    virtual task run_phase(uvm_phase phase);
        forever begin
            `uvm_info("DRV", "Waiting for Transaction..", UVM_NONE);
            seq_item_port.get_next_item(t);
            aif.a <= t.a;
            aif.b <= t.b;
            `uvm_info("DRV", "Transaction received.. Triggering DUT..", UVM_NONE)
            `uvm_info("DRV", $sformatf("Transaction Info: a=%0d , b=%0d", t.a, t.b), UVM_NONE)
            #10;
            seq_item_port.item_done();
        end
    endtask
endclass

//////////////////////////////////////////////////////////////////////////////////


