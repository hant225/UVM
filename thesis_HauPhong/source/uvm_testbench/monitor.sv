`timescale 1ns / 1ps
`include "uvm_macros.svh"
import uvm_pkg::*;

//////////////////////////////////////////////////////////////////////////////////

class monitor extends uvm_monitor;
    // Register to Factory
    `uvm_component_utils(monitor)
    
    // Properties   
    transaction tr;
    virtual pe_conv_mac_conv1_if vif;
    
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
        if(!uvm_config_db#(virtual pe_conv_mac_conv1_if)::get(this, "", "vif", vif))
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
                `uvm_info("MON", "SYSTEM RESET DETECTED", UVM_NONE);
            end 
            else begin
                    tr.rst          = 1'b0;
                    tr.load_weight  = vif.load_weight;  
                    tr.en           = vif.en;
                    tr.buffer_in_en = vif.buffer_in_en;                                 
                if(vif.load_weight) begin                                // weight load process
                    tr.weight_addr  = vif.weight_addr;
                    tr.weight_data  = vif.weight_data;
                    `uvm_info("MON", $sformatf("[MEMORY LOADING] Weight Loaded: weight_addr = %0h , weight_data = %8h_%8h", tr.weight_addr, tr.weight_data[63:32], tr.weight_data[31:0]), UVM_NONE)
                end 
                else if(!vif.load_weight) begin                          // pe_conv_mac process
                    @(posedge vif.valid)
                    tr.data_in      = vif.data_in;
                    tr.valid        = vif.valid;
                    tr.data_out     = vif.data_out;
                    tr.done         = vif.done;
                    tr.pe_ready     = vif.pe_ready;
                    tr.tr_display("MON");
                end
            end
            // Send to Scoreboard
            send.write(tr);
        end
    endtask: run_phase
    
endclass

