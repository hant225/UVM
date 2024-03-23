`timescale 1ns / 1ps
`include "uvm_macros.svh"
import uvm_pkg::*;

//////////////////////////////////////////////////////////////////////////////////

class monitor extends uvm_monitor;
    // Register to Factory
    `uvm_component_utils(monitor)
    
    // Properties   
    transaction tr;
    virtual pe_conv_mac_datapath_if vif;
    
    // Analysis Port
    uvm_analysis_port #(transaction) send;
    
    // Constructor
    function new(input string path = "MON", uvm_component parent = null);
        super.new(path, parent);
    endfunction
    
    // Build Phase
    virtual function void build_phase(uvm_phase phase);
        super.build_phase(phase);
        tr = transaction::type_id::create("tr");
        if(!uvm_config_db#(virtual pe_conv_mac_datapath_if)::get(this, "", "vif", vif))
            `uvm_error("MON", "UNABLE TO ACCESS THE INTERFACE!!!");
        send = new("send", this);
    endfunction
    
    // Run phase
    virtual task run_phase(uvm_phase phase);
        forever begin
            @(posedge vif.clk);           
            tr.op = vif.op;         
            if(tr.op == RESET) begin
                tr.rst = 1'b1;
                tr.clr = 1'b1;
                `uvm_info("MON", "SYSTEM RESET DETECTED", UVM_NONE);
            end 
            else begin
                    tr.rst         = 1'b0;
                    tr.clr         = 1'b0;       
                    tr.load_weight = vif.load_weight;                    
                    tr.weight_data = vif.weight_data;                    // data for kernel in load weight | data for dequantize scale
                if(vif.load_weight) begin                                // weight load process
                    tr.weight_addr = vif.weight_addr;
                    `uvm_info("MON",$sformatf("[MEMORY LOADING] Weight Loaded: weight_addr = %0h , weight_data = %0h", tr.weight_addr, tr.weight_data), UVM_NONE);
                end 
                else if(vif.load_weight == 0) begin                      // pe_conv_mac process
                    tr.en          = vif.en;  
                    tr.adder_en    = vif.adder_en;   
                    tr.dequant_en  = vif.dequant_en; 
                    tr.bias_en     = vif.bias_en;    
                    tr.act_en      = vif.act_en;     
                    tr.quant_en    = vif.quant_en;   
                    tr.kernel_addr = vif.kernel_addr;
                    tr.data_in     = vif.data_in;
                    repeat(23) @(posedge vif.clk);
                    tr.data_out    = vif.data_out;
                    mdisplay(tr);
                end
            end
            // Send to Scoreboard
            send.write(tr);
        end
    endtask: run_phase
    
    // Monitor Display Method
    task mdisplay(transaction tr);
        `uvm_info("MON", "--------------------------------------Transaction Info--------------------------------------", UVM_NONE)
        `uvm_info("MON", $sformatf("op          = %s", tr.op.name), UVM_NONE)
        `uvm_info("MON", $sformatf("rst         = %0h", tr.rst), UVM_NONE)
        `uvm_info("MON", $sformatf("clr         = %0h", tr.clr), UVM_NONE)
        `uvm_info("MON", $sformatf("load_weight = %0h", tr.load_weight), UVM_NONE)
        `uvm_info("MON", $sformatf("weight_data = %0h  (Scale if load_weight = 0)", tr.weight_data), UVM_NONE)
        `uvm_info("MON", $sformatf("en          = %0h", tr.en), UVM_NONE)
        `uvm_info("MON", $sformatf("adder_en    = %0h", tr.adder_en), UVM_NONE)
        `uvm_info("MON", $sformatf("dequant_en  = %0h", tr.dequant_en), UVM_NONE)
        `uvm_info("MON", $sformatf("bias_en     = %0h", tr.bias_en), UVM_NONE)
        `uvm_info("MON", $sformatf("act_en      = %0h", tr.act_en), UVM_NONE)
        `uvm_info("MON", $sformatf("quant_en    = %0h", tr.quant_en), UVM_NONE)
        `uvm_info("MON", $sformatf("data_in     = %0h", tr.data_in), UVM_NONE)
        `uvm_info("MON", $sformatf("kernel_addr = %0h", tr.kernel_addr), UVM_NONE)
        `uvm_info("MON", $sformatf("data_out    = %0h", tr.data_out), UVM_NONE)
        `uvm_info("MON", "--------------------------------------------------------------------------------------------", UVM_NONE)
    endtask
endclass


