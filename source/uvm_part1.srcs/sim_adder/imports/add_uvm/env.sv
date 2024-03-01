`timescale 1ns / 1ps
`include "uvm_macros.svh"
import uvm_pkg::*;

//////////////////////////////////////////////////////////////////////////////////

class env extends uvm_env;
    // Register to Factory
    `uvm_component_utils(env)
    
    // Properties
    agent a;
    scoreboard s;
    
    // Constructor
    function new(string path = "ENV", uvm_component parent = null);
        super.new(path, parent);
    endfunction
    
    // Build Phase
    virtual function void build_phase(uvm_phase phase);
        super.build_phase(phase);
        a = agent::type_id::create("a", this);
        s = scoreboard::type_id::create("s", this);
    endfunction
    
    // Connect Phase
    virtual function void connect_phase(uvm_phase phase);
        super.connect_phase(phase);
        a.m.send.connect(s.recv);
    endfunction
endclass

//////////////////////////////////////////////////////////////////////////////////

