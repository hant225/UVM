`timescale 1ns / 1ps
`include "uvm_macros.svh"
import uvm_pkg::*;

//////////////////////////////////////////////////////////////////////////////////
 
class l105_comp extends uvm_component;
    // Register to Factory
    `uvm_component_utils(l105_comp)
    
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
        phase.phase_done.set_drain_time(this, 200);        
        phase.raise_objection(this);
            `uvm_info("comp", "Main Phase Started", UVM_NONE);
            #100;
            `uvm_info("comp", "Main Phase Completed", UVM_NONE);
        phase.drop_objection(this);
    endtask
    
    task post_main_phase(uvm_phase phase);
        `uvm_info("comp", "Post_Main Phase Started", UVM_NONE);
    endtask
    
    // Build Phase;
    virtual function void build_phase(uvm_phase phase);
        super.build_phase(phase);
    endfunction
endclass
 
//////////////////////////////////////////////////////////////////////////////////


module section6_105;
    initial begin
//        uvm_top.set_timeout(100ns, 0);
        run_test("l105_comp");
    end
endmodule
