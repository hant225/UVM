`timescale 1ns / 1ps
`include "uvm_macros.svh"
import uvm_pkg::*;
import convDW_pkg::*;

//////////////////////////////////////////////////////////////////////////////////

class convDW_transaction extends conv1_transaction #(.pWEIGHT_DATA_WIDTH (convDW_pkg::pWEIGHT_DATA_WIDTH),
                                                     .pDATA_WIDTH        (convDW_pkg::pDATA_WIDTH),
                                                     .pIN_CHANNEL        (convDW_pkg::pIN_CHANNEL),
                                                     .pOUT_CHANNEL       (convDW_pkg::pOUT_CHANNEL));    
    
    // Constructor
    function new(input string path = "convDW_transaction");
        super.new(path);
    endfunction    
        
    // Field Macros
    `uvm_object_utils_begin(convDW_transaction)
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
    
endclass