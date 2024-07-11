`timescale 1ns / 1ps
`include "uvm_macros.svh"
import uvm_pkg::*;

//////////////////////////////////////////////////////////////////////////////////

class conv1_env extends uvm_env;
    // Register to Factory
    `uvm_component_utils(conv1_env)
    
    // Properties
    conv1_scoreboard s;
    conv1_agent      a;
    
    // Constructor
    function new(input string path = "ENV", uvm_component parent = null);
        super.new(path, parent);       
    endfunction
    
    // Build Phase
    virtual function void build_phase(uvm_phase phase);
        super.build_phase(phase);
        s = conv1_scoreboard::type_id::create("s", this);
        a = conv1_agent::type_id::create("a", this);
    endfunction
    
    // Connect Phase
    virtual function void connect_phase(uvm_phase phase);
        a.m.send.connect(s.recv);
    endfunction
endclass
