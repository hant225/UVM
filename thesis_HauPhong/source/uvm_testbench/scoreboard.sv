`timescale 1ns / 1ps
`include "uvm_macros.svh"
import uvm_pkg::*;

//////////////////////////////////////////////////////////////////////////////////

class scoreboard extends uvm_monitor;
    // Register to Factory
    `uvm_component_utils(scoreboard)
   
    // Properties
   
    // Analysis Imp
    uvm_analysis_imp #(transaction, scoreboard) recv;
    
    // Constructor
    function new(input string path = "SCB", uvm_component parent = null);
        super.new(path, parent);
    endfunction
    
    // Build Phase
    virtual function void build_phase(uvm_phase phase);
        super.build_phase(phase);
        recv = new("recv", this);
    endfunction
    
    // Write Method
    virtual function void write(transaction tr);
        if(tr.rst || tr.clr)
            `uvm_info("SCB", "SYSTEM RESET", UVM_NONE)
        else begin 
            if(tr.load_weight) 
                mirror_mem(tr);
            else 
                checking_result(tr);
        end
    endfunction   
    
    // Mirroring Ram Method
    function void mirror_mem(transaction tr);
        `uvm_info("SCB", $sformatf("[MEMORY MIRROR]  Weight Loaded: weight_addr = %0h , weight_data = %0h\n", tr.weight_addr, tr.weight_data), UVM_NONE);
    endfunction
    
    // Result Checking Method
    function void checking_result(transaction tr);
        $display("CHECKING RESULT HERE");
        sdisplay(tr);
    endfunction
    
    // Display Method
    function void sdisplay(transaction tr);
        `uvm_info("SCB", "--------------------------------------Transaction Info--------------------------------------", UVM_NONE)
        `uvm_info("SCB", $sformatf("rst         = %0h", tr.rst), UVM_NONE)
        `uvm_info("SCB", $sformatf("clr         = %0h", tr.clr), UVM_NONE)
        `uvm_info("SCB", $sformatf("load_weight = %0h", tr.load_weight), UVM_NONE)
        `uvm_info("SCB", $sformatf("en          = %0h", tr.en), UVM_NONE)
        `uvm_info("SCB", $sformatf("adder_en    = %0h", tr.adder_en), UVM_NONE)
        `uvm_info("SCB", $sformatf("dequant_en  = %0h", tr.dequant_en), UVM_NONE)
        `uvm_info("SCB", $sformatf("bias_en     = %0h", tr.bias_en), UVM_NONE)
        `uvm_info("SCB", $sformatf("act_en      = %0h", tr.act_en), UVM_NONE)
        `uvm_info("SCB", $sformatf("quant_en    = %0h", tr.quant_en), UVM_NONE)
        `uvm_info("SCB", $sformatf("weight_addr = %0h", tr.weight_addr), UVM_NONE)
        `uvm_info("SCB", $sformatf("weight_data = %0h  (Scale if load_weight = 0)", tr.weight_data), UVM_NONE)
        `uvm_info("SCB", $sformatf("data_in     = %0h", tr.data_in), UVM_NONE)
        `uvm_info("SCB", $sformatf("kernel_addr = %0h", tr.kernel_addr), UVM_NONE)
        `uvm_info("SCB", $sformatf("data_out    = %0h", tr.data_out), UVM_NONE)
        `uvm_info("SCB", "--------------------------------------------------------------------------------------------", UVM_NONE)
    endfunction
endclass


