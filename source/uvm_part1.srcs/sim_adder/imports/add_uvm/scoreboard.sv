`timescale 1ns / 1ps
`include "uvm_macros.svh"
import uvm_pkg::*;

//////////////////////////////////////////////////////////////////////////////////

class scoreboard extends uvm_scoreboard;
    // Register to Factory
    `uvm_component_utils(scoreboard)
    
    // Properties
    transaction tc;
    uvm_analysis_imp #(transaction, scoreboard) recv;
    
    // Constructor
    function new(string path = "SCB", uvm_component parent = null);
        super.new(path, parent);
        recv = new("recv", this);
    endfunction
    
    // Build Phase
    virtual function void build_phase(uvm_phase phase);
        super.build_phase(phase);
        tc = transaction::type_id::create("tc");
    endfunction
    
    // Write Method
    virtual function void write(transaction t);
        this.tc = t;
        `uvm_info("SCB", $sformatf("Data Rcvd from SCB: a=%0d , b=%0d , y=%0d", tc.a, tc.b, tc.y), UVM_NONE);
        if (tc.y == tc.a + tc.b)
            `uvm_info("SCB", "Test Passed", UVM_NONE)
        else
            `uvm_info("SCB", "Test Failed", UVM_NONE)
    endfunction
endclass

//////////////////////////////////////////////////////////////////////////////////



