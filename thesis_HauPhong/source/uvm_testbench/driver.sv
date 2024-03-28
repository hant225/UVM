`timescale 1ns / 1ps
`include "uvm_macros.svh"
import uvm_pkg::*;

//////////////////////////////////////////////////////////////////////////////////

class driver extends uvm_driver#(transaction);
    // Register to Factory
    `uvm_component_utils(driver)
    
    // Properties   
    transaction tr;
    virtual pe_conv_mac_conv1_if vif;
    
    // Constructor
    function new(input string path = "DRV", uvm_component parent = null);
        super.new(path, parent);
    endfunction
    
    // Build Phase
    virtual function void build_phase(uvm_phase phase);
        super.build_phase(phase);
        tr = transaction::type_id::create("tr");
        if(!uvm_config_db#(virtual pe_conv_mac_conv1_if)::get(this, "", "vif", vif))
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
                    vif.op           <= tr.op;
                    vif.rst          <= tr.rst; 
                    vif.load_weight  <= tr.load_weight;                             
                if(tr.load_weight) begin
                    vif.weight_addr  <= tr.weight_addr; 
                    vif.weight_data  <= tr.weight_data;
                    vif.en           <= 1'b0;
                    vif.buffer_in_en <= 1'b1;
                    @(posedge vif.clk);  
                    `uvm_info("DRV", $sformatf("[MEMORY LOADING] Weight Loaded: weight_addr = %0h , weight_data = %8h_%8h", tr.weight_addr, tr.weight_data[63:32], tr.weight_data[31:0],), UVM_NONE)
                end 
                else if(!tr.load_weight) begin
                    vif.en           <= tr.en;
                    vif.buffer_in_en <= tr.buffer_in_en;
                    vif.data_in      <= tr.data_in;
                    tr.tr_display("DRV");
                    @(posedge vif.clk);             // wait one cycle for loading data_in to buffer_in
                    vif.buffer_in_en <= 1'b0;
                    `uvm_info("DRV", $sformatf("Deassert buffer_in_en : %0b", vif.buffer_in_en), UVM_NONE);
                    repeat(10) @(posedge vif.clk);
                end
            seq_item_port.item_done(tr);
        end
    endtask
    
    
    // DUT reset
    task reset_DUT();
        repeat(5) begin 
            vif.op          <= RESET;
            vif.rst         <= 1'b1;
            @(posedge vif.clk);
        end
        `uvm_info("DRV", "SYSTEM RESET: START OF SIMULATION", UVM_NONE)
    endtask
    
endclass

