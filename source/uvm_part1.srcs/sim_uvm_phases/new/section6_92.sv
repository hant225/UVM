`timescale 1ns / 1ps
`include "uvm_macros.svh"
import uvm_pkg::*;

//////////////////////////////////////////////////////////////////////////////////

class test extends uvm_component;
    // Register to Factory
    `uvm_component_utils(test)
    
    // Constructor
    function new(string path = "test", uvm_component parent = null);
        super.new(path, parent);
    endfunction
    
    // CONSTRUCTION PHASES
    //// Build Phase
    virtual function void build_phase(uvm_phase phase);
        super.build_phase(phase);
        `uvm_info("test", "Build Phase Executed", UVM_NONE)
    endfunction
    
    //// Connect Phase
    virtual function void connect_phase(uvm_phase phase);
        super.connect_phase(phase);
        `uvm_info("test", "Connect Phase Executed", UVM_NONE)
    endfunction
    
    //// End of elaboration Phase
    virtual function void end_of_elaboration_phase(uvm_phase phase);
        super.end_of_elaboration_phase(phase);
        `uvm_info("test", "End of elaboration Phase Executed", UVM_NONE)
    endfunction
    
    //// Start of simulation Phase
    virtual function void start_of_simulation_phase(uvm_phase phase);
        super.start_of_simulation_phase(phase);
        `uvm_info("test", "Start of simulation Phase Executed", UVM_NONE)
    endfunction
    
    // MAIN PHASES
    //// Run Phase
    task run_phase(uvm_phase phase);
        `uvm_info("test", "Run Phase", UVM_NONE)
    endtask 
    
    // CLEANUP PHASE
    //// Extract Phase
    virtual function void extract_phase(uvm_phase phase);
        super.extract_phase(phase);
        `uvm_info("test", "Extract Phase", UVM_NONE)
    endfunction
    
    //// Check Phase
    virtual function void check_phase(uvm_phase phase);
        super.check_phase(phase);
        `uvm_info("test", "Check Phase", UVM_NONE)
    endfunction
    
    //// Report Phase
    virtual function void report_phase(uvm_phase phase);
        super.report_phase(phase);
        `uvm_info("test", "Report Phase", UVM_NONE)
    endfunction
    
    //// Final Phase
    virtual function void final_phase(uvm_phase phase);
        super.final_phase(phase);
        `uvm_info("test", "Final Phase", UVM_NONE)
    endfunction
endclass
 
//////////////////////////////////////////////////////////////////////////////////

module section6_92;
    initial begin
        run_test("test");
    end
endmodule
