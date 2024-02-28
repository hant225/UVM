`timescale 1ns / 1ps
`include "uvm_macros.svh"
import uvm_pkg::*;
//////////////////////////////////////////////////////////////////////////////////

class a extends uvm_component;
    // Register to Factory 
    `uvm_component_utils(a)
    
    // Constructor
    function new(string path = "a", uvm_component parent = null);
        super.new(path, parent);
    endfunction

    // Build Phase
    virtual function void build_phase(uvm_phase phase);
        super.build_phase(phase);
        `uvm_info("a", "Class a executed", UVM_NONE)
    endfunction
endclass

//////////////////////////////////////////////////////////////////////////////////

class b extends uvm_component;
    // Register to Factory 
    `uvm_component_utils(b)
    
    // Constructor
    function new(string path = "b", uvm_component parent = null);
        super.new(path, parent);
    endfunction

    // Build Phase
    virtual function void build_phase(uvm_phase phase);
        super.build_phase(phase);
        `uvm_info("b", "Class b executed", UVM_NONE)
    endfunction
endclass

//////////////////////////////////////////////////////////////////////////////////

class c extends uvm_component;
    // Register to Factory 
    `uvm_component_utils(c)
    
    // Properties
    a a_inst;
    b b_inst;
    
    // Constructor
    function new(string path = "c", uvm_component parent = null);
        super.new(path, parent);
    endfunction

    // Build Phase
    virtual function void build_phase(uvm_phase phase);
        super.build_phase(phase);
        a_inst = a::type_id::create("a", this);
        b_inst = b::type_id::create("b", this);
    endfunction
    
    // End of elaboration Phase
    virtual function void end_of_elaboration_phase(uvm_phase phase);
        super.end_of_elaboration_phase(phase);
        uvm_top.print_topology();
    endfunction
endclass

//////////////////////////////////////////////////////////////////////////////////

module section4_72;

    initial begin
        run_test("c");
    end
    
endmodule
