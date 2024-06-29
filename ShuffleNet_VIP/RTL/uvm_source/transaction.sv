`timescale 1ns / 1ps
`include "uvm_macros.svh"
import uvm_pkg::*;

//////////////////////////////////////////////////////////////////////////////////
typedef enum bit[3:0] {RESET, 
                       MEM_KERNEL_LOAD, 
                       MEM_BIAS_LOAD, 
                       MEM_DEQUANT_SCALE_LOAD,
                       MEM_QUANT_SCALE_LOAD, 
                       LOAD_PIXELS,
                       PE_RUNNING} oper_mode;            
                        
class transaction extends uvm_sequence_item;
    // Local Parameter
    localparam pDATA_WIDTH        = 8;
    localparam pWEIGHT_DATA_WIDTH = 64;
    localparam pIN_CHANNEL        = 3;
    localparam pOUT_CHANNEL       = 24;

    // Properties
    oper_mode op;
         logic                                rst;
         logic                                en;        
         logic                                load_weight;
    rand logic [31:0]                         weight_addr;
    rand logic [pWEIGHT_DATA_WIDTH-1:0]       weight_data;
    rand logic [pDATA_WIDTH*pIN_CHANNEL-1:0]  data_in;
         logic [pDATA_WIDTH*pOUT_CHANNEL-1:0] data_out;
         logic                                valid;
         logic                                done;                  
    
    // Constraint
    constraint cred   {data_in[23:16] == 8'hff;}
    constraint cblue  {data_in[15:8]  == 8'h00;}
    constraint cgreen {data_in[7:0]   == 8'h00;}
    
    // Constructor
    function new(input string path = "transaction");
        super.new(path);
    endfunction
    
    // Field Macros
    `uvm_object_utils_begin(transaction)
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
            `uvm_info(class_name, $sformatf("data_out = %0h", this.data_out), UVM_NONE)
            `uvm_info(class_name, $sformatf("valid    = %0b", this.valid), UVM_NONE)
            `uvm_info(class_name, $sformatf("done     = %0b", this.done), UVM_NONE)            
        end
        `uvm_info(class_name, "--------------------------------------------------------------------------------------------", UVM_NONE)
    endfunction
endclass


