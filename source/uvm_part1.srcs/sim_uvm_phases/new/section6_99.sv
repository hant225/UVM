`timescale 1ns/1ns
`include "uvm_macros.svh"
import uvm_pkg::*;

//////////////////////////////////////////////////////////////////////////////////

class comp extends uvm_component;
    // Register to Factory
    `uvm_component_utils(comp)
    
    // Constructor
    function new(string path = "comp", uvm_component parent = null);
        super.new(path, parent);
    endfunction
    
    //// RUN PHASES
    // Reset Phase
    task reset_phase(uvm_phase phase);
        phase.raise_objection(this);
            `uvm_info("comp", "Reset started", UVM_NONE);
            #10; // Do reset
            `uvm_info("comp", "Reset completed", UVM_NONE);
        phase.drop_objection(this);
    endtask
    
    // Main Phase
    task main_phase(uvm_phase phase);
        phase.raise_objection(this);
            `uvm_info("comp", "Main Phase Started", UVM_NONE);
            #100;
            `uvm_info("comp", "Main Phase Completed", UVM_NONE);
        phase.drop_objection(this);
    endtask
endclass

//////////////////////////////////////////////////////////////////////////////////

module section6_99;
    initial begin
        run_test("comp");
    end
endmodule
