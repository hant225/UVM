`timescale 1ns / 1ps
`include "uvm_macros.svh"
import uvm_pkg::*;

//////////////////////////////////////////////////////////////////////////////////

class transaction extends uvm_sequence_item;
    // Properties
    rand bit [3:0] a;
    rand bit [3:0] b;
         bit [4:0] y;
    
    // Constructor
    function new(string inst = "transaction");
        super.new(inst);
    endfunction
    
    // Field Macro
    `uvm_object_utils_begin(transaction);
        `uvm_field_int(a, UVM_DEFAULT);
        `uvm_field_int(b, UVM_DEFAULT);
        `uvm_field_int(y, UVM_DEFAULT);
    `uvm_object_utils_end
endclass

//////////////////////////////////////////////////////////////////////////////////

interface add_if();
    logic [3:0] a;
    logic [3:0] b;
    logic [4:0] y;
endinterface

