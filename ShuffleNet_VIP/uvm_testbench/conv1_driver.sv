`timescale 1ns / 1ps
`include "uvm_macros.svh"
import uvm_pkg::*;

//////////////////////////////////////////////////////////////////////////////////

class conv1_driver extends uvm_driver#(conv1_transaction);
    // Register to Factory
    `uvm_component_utils(conv1_driver)
    
    // Properties   
    conv1_transaction tr;
    virtual conv1_if vif;
    
    // Constructor
    function new(input string path = "DRV", uvm_component parent = null);
        super.new(path, parent);
    endfunction
    
    // Build Phase
    virtual function void build_phase(uvm_phase phase);
        super.build_phase(phase);
        tr = conv1_transaction::type_id::create("tr");
        if(!uvm_config_db#(virtual conv1_if)::get(this, "", "vif", vif))
            `uvm_error("DRV", "UNABLE TO ACCESS THE INTERFACE!!!")
    endfunction
    
    // Run phase
    virtual task run_phase(uvm_phase phase);
        drive(tr);
    endtask
    
    // Methods
    virtual task drive(conv1_transaction tr);
        reset_DUT();
        forever begin
            seq_item_port.get_next_item(tr);   
                    vif.op           <= tr.op;
                    vif.rst          <= tr.rst; 
                    vif.load_weight  <= tr.load_weight;                             
                if(tr.load_weight) begin
                    vif.weight_addr  <= tr.weight_addr; 
                    vif.weight_data  <= tr.weight_data;
                    vif.data_in      <= 'dx;
                    vif.en           <= 1'b0;                                        
                    @(posedge vif.clk);  
                    `uvm_info("DRV", $sformatf("[%s] Weight Loaded: weight_addr = %0h , weight_data = %16h", tr.op.name, tr.weight_addr, tr.weight_data), UVM_NONE)
                end 
                else if(!tr.load_weight) begin
                    vif.weight_addr  <= 'dx;
                    vif.weight_data  <= 'dx;
                    vif.en           <= tr.en;
                    vif.data_in      <= tr.data_in;
                    tr.tr_display("DRV");
                    @(posedge vif.clk);
                end
            seq_item_port.item_done(tr);
        end
    endtask
    
    
    // DUT reset
    virtual task reset_DUT();
        repeat(5) begin 
            vif.op  <= RESET;
            vif.rst <= 1'b1;
            @(posedge vif.clk);
        end
        `uvm_info("DRV", "SYSTEM RESET: START OF SIMULATION", UVM_NONE)
    endtask
    
endclass
