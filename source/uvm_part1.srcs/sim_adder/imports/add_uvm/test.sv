`timescale 1ns / 1ps
`include "uvm_macros.svh"
import uvm_pkg::*;

//////////////////////////////////////////////////////////////////////////////////

class test extends uvm_test;
    // Register to Factory
    `uvm_component_utils(test)
    
    // Properties
    sequence1 seq;
    env e;
    
    // Constructor
    function new(string path = "TEST", uvm_component parent = null);
        super.new(path, parent);
    endfunction
    
    // Build Phase
    virtual function void build_phase(uvm_phase phase);
        super.build_phase(phase);
        seq = sequence1::type_id::create("seq", this);
        e   = env::type_id::create("e", this);
    endfunction
    
    // Run Phase
    virtual task run_phase(uvm_phase phase);
        phase.raise_objection(this);
        seq.start(e.a.seqr);
        phase.drop_objection(this);
    endtask
endclass

//////////////////////////////////////////////////////////////////////////////////

