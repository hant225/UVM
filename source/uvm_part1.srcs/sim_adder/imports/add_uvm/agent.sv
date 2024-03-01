`timescale 1ns / 1ps
`include "uvm_macros.svh"
import uvm_pkg::*;

//////////////////////////////////////////////////////////////////////////////////

class agent extends uvm_agent;
    // Register to Factory
    `uvm_component_utils(agent)
    
    // Properties
    driver d;
    monitor m;
    uvm_sequencer#(transaction) seqr;
    
    // Constructor
    function new(string path = "AGENT", uvm_component parent = null);
        super.new(path, parent);
    endfunction
    
    // Build Phase
    virtual function void build_phase(uvm_phase phase);
        super.build_phase(phase);
        d = driver::type_id::create("d", this);
        m = monitor::type_id::create("m", this);
        seqr = uvm_sequencer#(transaction)::type_id::create("seqr", this);
    endfunction
    
    // Connect Phase
    virtual function void connect_phase(uvm_phase phase);
        super.connect_phase(phase);
        d.seq_item_port.connect(seqr.seq_item_export);
    endfunction
endclass


//////////////////////////////////////////////////////////////////////////////////

