`timescale 1ns / 1ps
`include "uvm_macros.svh"
import uvm_pkg::*;

//////////////////////////////////////////////////////////////////////////////////

class monitor extends uvm_monitor;
    // Register to Factory
    `uvm_component_utils(monitor)
    
    // Properties   
    transaction tr;
    virtual conv1_if vif;  
    int valid_count = 0;  
    
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
        if(!uvm_config_db#(virtual conv1_if)::get(this, "", "vif", vif))
            `uvm_error("MON", "UNABLE TO ACCESS THE INTERFACE!!!");
        send = new("send", this);
    endfunction
    
    // Run phase
    virtual task run_phase(uvm_phase phase);
        phase.raise_objection(this);        
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
                if(vif.load_weight) begin                        // weight load process
                    tr.weight_addr  = vif.weight_addr;
                    tr.weight_data  = vif.weight_data;
                    tr.data_in      = 'dx;
                    `uvm_info("MON", $sformatf("[%s] Weight Loaded: weight_addr = %0h , weight_data = %16h", tr.op.name, tr.weight_addr, tr.weight_data), UVM_NONE)
                end 
                else if(!vif.load_weight) begin                       // pe_conv_mac process                            
                    tr.data_in      = vif.data_in;
                    tr.data_out     = vif.data_out;
                    tr.valid        = vif.valid;                    
                    tr.done         = vif.done;                                        
                end                                                      
            end            
            // Send to Scoreboard
            send.write(tr);
            // Stop Run Phase
            if(tr.valid) begin
                valid_count = valid_count + 1;
                tr.tr_display("MON");
                `uvm_info("MON", $sformatf("No. Valid : %0d", valid_count), UVM_NONE)
            end            
            
            if(valid_count == 12543)        // out feature map
                phase.drop_objection(this);
        end
    endtask: run_phase
    
    
endclass

