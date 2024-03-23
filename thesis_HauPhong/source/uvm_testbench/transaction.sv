`timescale 1ns / 1ps
`include "uvm_macros.svh"
import uvm_pkg::*;

//////////////////////////////////////////////////////////////////////////////////
typedef enum bit[3:0] { RESET,
                        MEM_KERNEL_LOAD,
                        MEM_BIAS_LOAD,
                        MEM_SCALE_LOAD,
                        DATA_IN_LOAD} oper_mode;
                        
                        
class transaction extends uvm_sequence_item;
    // Properties
    oper_mode op;
          logic         rst;
          logic         clr;
          logic         load_weight;
          logic [31:0]  weight_addr;
    rand  logic [63:0]  weight_data;
    randc logic [3:0]   kernel_addr;        
          logic         en;
          logic         adder_en;
          logic         dequant_en;
          logic         bias_en;
          logic         act_en;
          logic         quant_en;
     rand logic [7:0]   data_in;
          logic [255:0] data_out;
    
    // Constraint
    constraint kernel_addr_c {kernel_addr inside {[0:8]};}
    
    // Constructor
    function new(input string path = "transaction");
        super.new(path);
    endfunction
    
    // Field Macros
    `uvm_object_utils_begin(transaction)
        `uvm_field_int(rst,         UVM_DEFAULT)
        `uvm_field_int(clr,         UVM_DEFAULT)
        `uvm_field_int(load_weight, UVM_DEFAULT)
        `uvm_field_int(weight_addr, UVM_DEFAULT)
        `uvm_field_int(weight_data, UVM_DEFAULT)
        `uvm_field_int(kernel_addr, UVM_DEFAULT)
        `uvm_field_int(en,          UVM_DEFAULT)
        `uvm_field_int(adder_en,    UVM_DEFAULT)
        `uvm_field_int(dequant_en,  UVM_DEFAULT)
        `uvm_field_int(bias_en,     UVM_DEFAULT)
        `uvm_field_int(act_en,      UVM_DEFAULT)
        `uvm_field_int(quant_en,    UVM_DEFAULT)
        `uvm_field_int(data_in,     UVM_DEFAULT)
        `uvm_field_int(data_out,    UVM_DEFAULT)      
    `uvm_object_utils_end
endclass



