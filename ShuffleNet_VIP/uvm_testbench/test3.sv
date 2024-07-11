`timescale 1ns / 1ps
`include "uvm_macros.svh"
import uvm_pkg::*;

//////////////////////////////////////////////////////////////////////////////////////

class base_seq#(parameter pDATA_WIDTH        = 8,
                parameter pWEIGHT_DATA_WIDTH = 3,
                parameter pCONV1_IN_CHANNEL  = 3,
                parameter pCONV1_OUT_CHANNEL = 7) extends uvm_sequence_item;
    // Properties
    rand logic [31:0]                               weight_addr;
    rand logic [pWEIGHT_DATA_WIDTH-1:0]             weight_data;
    rand logic [pDATA_WIDTH*pCONV1_IN_CHANNEL-1:0]  data_in;
    rand logic [pDATA_WIDTH*pCONV1_OUT_CHANNEL-1:0] data_out;
                 
    
    // Constructor
    function new(input string path = "base_seq");
        super.new(path);
    endfunction
    
    // Field Macros
    `uvm_object_utils_begin(base_seq)       
        `uvm_field_int (weight_addr,   UVM_DEFAULT)
        `uvm_field_int (weight_data,   UVM_DEFAULT)
        `uvm_field_int (data_in,       UVM_DEFAULT)
        `uvm_field_int (data_out,      UVM_DEFAULT)          
    `uvm_object_utils_end        
endclass

//////////////////////////////////////////////////////////////////////////////////////

class child_seq extends base_seq#(.pDATA_WIDTH        (16),
                                     .pWEIGHT_DATA_WIDTH (6),
                                     .pCONV1_IN_CHANNEL  (6),
                                     .pCONV1_OUT_CHANNEL (14));    
    // Factory Register                                 
    `uvm_object_utils(child_seq)                       
                                         
    // Constructor
    function new(input string path = "child_seq");
        super.new(path);
    endfunction    
endclass
//////////////////////////////////////////////////////////////////////////////////////

module test3;
    base_seq  bs;
    child_seq cs;
    
    initial begin
        bs = base_seq::type_id::create("bs");
        cs = child_seq::type_id::create("cs");
        bs.randomize();
        cs.randomize();
        `uvm_info("BASE_SEQ", $sformatf("size of bs.weight_data = %0d", $size(bs.weight_data)), UVM_NONE)
        `uvm_info("CHILD_SEQ", $sformatf("size of cs.weight_data = %0d", $size(cs.weight_data)), UVM_NONE)
    end
endmodule
