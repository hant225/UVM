`timescale 1ns / 1ps
`include "uvm_macros.svh"
import uvm_pkg::*;
import conv1_pkg::*;            
           
//////////////////////////////////////////////////////////////////////////////////
                        
class conv1_transaction #(localparam pWEIGHT_DATA_WIDTH = conv1_pkg::pWEIGHT_DATA_WIDTH,
                          localparam pDATA_WIDTH        = conv1_pkg::pDATA_WIDTH,
                          localparam pIN_CHANNEL        = conv1_pkg::pIN_CHANNEL,
                          localparam pOUT_CHANNEL       = conv1_pkg::pOUT_CHANNEL) extends uvm_sequence_item;

    // Properties
    oper_mode op;
    logic                                rst;
    logic                                en;        
    logic                                load_weight;
    logic [31:0]                         weight_addr;
    logic [pWEIGHT_DATA_WIDTH-1:0]       weight_data;
    logic [pDATA_WIDTH*pIN_CHANNEL-1:0]  data_in;
    logic [pDATA_WIDTH*pOUT_CHANNEL-1:0] data_out;
    logic                                valid;
    logic                                done;                  
    
    // Constructor
    function new(input string path = "conv1_transaction");
        super.new(path);
    endfunction
    
    // Field Macros
    `uvm_object_utils_begin(conv1_transaction)
        `uvm_field_enum(oper_mode, op, UVM_DEFAULT)
        `uvm_field_int (rst,           UVM_DEFAULT)
        `uvm_field_int (en,            UVM_DEFAULT)               
        `uvm_field_int (load_weight,   UVM_DEFAULT)
        `uvm_field_int (weight_addr,   UVM_DEFAULT)
        `uvm_field_int (weight_data,   UVM_DEFAULT)
        `uvm_field_int (data_in,       UVM_DEFAULT)
        `uvm_field_int (data_out,      UVM_DEFAULT)
        `uvm_field_int (valid,         UVM_DEFAULT)
        `uvm_field_int (done,          UVM_DEFAULT)        
    `uvm_object_utils_end
    
    // Display Method
    function void tr_display(string class_name);
        if(class_name != "DRV" && class_name != "MON" && class_name != "SCB")
            `uvm_error("SEQ_ITEM", $sformatf("%0s IS AN ILLEGAL CLASS NAME", class_name))
            
        `uvm_info(class_name, "--------------------------------------Transaction Info--------------------------------------", UVM_NONE)
        `uvm_info(class_name, $sformatf("op           = %s",  this.op.name), UVM_NONE)
        `uvm_info(class_name, $sformatf("en           = %0b", this.en), UVM_NONE)              
        `uvm_info(class_name, $sformatf("load_weight  = %0b", this.load_weight), UVM_NONE)
        `uvm_info(class_name, $sformatf("weight_addr  = %0h - dunkare", this.weight_addr), UVM_NONE)
        `uvm_info(class_name, $sformatf("weight_data  = %0h - dunkare", this.weight_data), UVM_NONE)
        `uvm_info(class_name, $sformatf("data_in      = %0h", this.data_in), UVM_NONE)
        if(class_name == "MON" || class_name == "SCB") begin
            `uvm_info(class_name, $sformatf("data_out     = %0h", this.data_out), UVM_NONE)
            `uvm_info(class_name, $sformatf("valid        = %0b", this.valid), UVM_NONE)
            `uvm_info(class_name, $sformatf("done         = %0b", this.done), UVM_NONE)                        
        end
        `uvm_info(class_name, "--------------------------------------------------------------------------------------------", UVM_NONE)
    endfunction
endclass

