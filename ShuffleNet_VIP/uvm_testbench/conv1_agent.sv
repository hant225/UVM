`timescale 1ns / 1ps
`include "uvm_macros.svh"
import uvm_pkg::*;

//////////////////////////////////////////////////////////////////////////////////

class conv1_agent extends uvm_agent;
    // Register to Factory
    `uvm_component_utils(conv1_agent)
    
    // Properties
    conv1_driver  d;
    conv1_monitor m;
    uvm_sequencer #(conv1_transaction) seqr;
    
    // Constructor
    function new(input string path = "AGENT", uvm_component parent = null);
        super.new(path, parent);       
    endfunction
    
    // Build Phase
    virtual function void build_phase(uvm_phase phase);
        super.build_phase(phase);
        d    = conv1_driver::type_id::create("d", this);
        m    = conv1_monitor::type_id::create("m", this);
        seqr = uvm_sequencer#(conv1_transaction)::type_id::create("seqr", this);
    endfunction
    
    // Connect Phase
    virtual function void connect_phase(uvm_phase phase);
        super.connect_phase(phase);
        d.seq_item_port.connect(seqr.seq_item_export);
    endfunction
endclass
