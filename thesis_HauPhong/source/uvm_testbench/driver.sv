`timescale 1ns / 1ps
`include "uvm_macros.svh"
import uvm_pkg::*;

//////////////////////////////////////////////////////////////////////////////////
// DSP needs 5 cycles
// adder + store need 1 cycles
// adder tree assump need 1 cycles (one pixel)
// dequantize needs 9 cycles
// bias needs 1 cycle
// activation needs 3 cycles
// quantize need 1 cycles
// 5 + 1 + 1 + 9 + 1 + 3 + 1 = 20 cycles to get data_out result
//////////////////////////////////////////////////////////////////////////////////

class driver extends uvm_driver#(transaction);
    // Register to Factory
    `uvm_component_utils(driver)
    
    // Properties   
    transaction tr;
    virtual pe_conv_mac_datapath_if vif;
    
    // Constructor
    function new(input string path = "DRV", uvm_component parent = null);
        super.new(path, parent);
    endfunction
    
    // Build Phase
    virtual function void build_phase(uvm_phase phase);
        super.build_phase(phase);
        tr = transaction::type_id::create("tr");
        if(!uvm_config_db#(virtual pe_conv_mac_datapath_if)::get(this, "", "vif", vif))
            `uvm_error("DRV", "UNABLE TO ACCESS THE INTERFACE!!!")
    endfunction
    
    // Run phase
    virtual task run_phase(uvm_phase phase);
        drive();
    endtask
    
    // Methods
    task drive();
        reset_DUT();
        forever begin
            seq_item_port.get_next_item(tr);   
                vif.op          <= tr.op;
                vif.rst         <= 1'b0;
                vif.clr         <= 1'b0;                
                vif.weight_data <= tr.weight_data;      // data for kernel in load weight | data for dequantize scale            
                if(tr.load_weight) begin
                    vif.load_weight <= 1'b1;
                    vif.weight_addr <= tr.weight_addr;  
                    @(posedge vif.clk);  
                    `uvm_info("DRV", $sformatf("[MEMORY LOADING] Weight Loaded: weight_addr = %0h , weight_data = %0h", tr.weight_addr, tr.weight_data), UVM_NONE)
                end 
                else if(!tr.load_weight) begin
                    `uvm_info("DRV", "Triggering DUT..", UVM_NONE)                                    
                    vif.load_weight <= 1'b0;
                    vif.en          <= tr.en;         
                    vif.adder_en    <= tr.adder_en;   
                    vif.dequant_en  <= tr.dequant_en; 
                    vif.bias_en     <= tr.bias_en;    
                    vif.act_en      <= tr.act_en;     
                    vif.quant_en    <= tr.quant_en;   
                    vif.kernel_addr <= tr.kernel_addr;
                    vif.data_in     <= tr.data_in; 
                    ddisplay(tr);
                    repeat(23) @(posedge vif.clk);
                end
            seq_item_port.item_done(tr);
        end
    endtask
    
    
    // DUT reset
    task reset_DUT();
        repeat(5) begin 
            vif.op          <= RESET;
            vif.rst         <= 1'b1;
            vif.clr         <= 1'b1;
            @(posedge vif.clk);
        end
        `uvm_info("DRV", "SYSTEM RESET: START OF SIMULATION", UVM_NONE)
    endtask
    
    // Driver Display()
    task ddisplay(transaction tr);
        `uvm_info("DRV", "--------------------------------------Transaction Info--------------------------------------", UVM_NONE)
        `uvm_info("DRV", $sformatf("op          = %s", tr.op.name), UVM_NONE)
        `uvm_info("DRV", $sformatf("rst         = %0h", tr.rst), UVM_NONE)
        `uvm_info("DRV", $sformatf("clr         = %0h", tr.clr), UVM_NONE)
        `uvm_info("DRV", $sformatf("load_weight = %0h", tr.load_weight), UVM_NONE)
        `uvm_info("DRV", $sformatf("weight_data = %0h  (Scale if load_weight = 0)", tr.weight_data), UVM_NONE)
        `uvm_info("DRV", $sformatf("en          = %0h", tr.en), UVM_NONE)
        `uvm_info("DRV", $sformatf("adder_en    = %0h", tr.adder_en), UVM_NONE)
        `uvm_info("DRV", $sformatf("dequant_en  = %0h", tr.dequant_en), UVM_NONE)
        `uvm_info("DRV", $sformatf("bias_en     = %0h", tr.bias_en), UVM_NONE)
        `uvm_info("DRV", $sformatf("act_en      = %0h", tr.act_en), UVM_NONE)
        `uvm_info("DRV", $sformatf("quant_en    = %0h", tr.quant_en), UVM_NONE)
        `uvm_info("DRV", $sformatf("data_in     = %0h", tr.data_in), UVM_NONE)
        `uvm_info("DRV", $sformatf("kernel_addr = %0h", tr.kernel_addr), UVM_NONE)
        `uvm_info("DRV", "--------------------------------------------------------------------------------------------", UVM_NONE)
    endtask
endclass


