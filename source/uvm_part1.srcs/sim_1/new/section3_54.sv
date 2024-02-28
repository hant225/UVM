`timescale 1ns / 1ps
`include "uvm_macros.svh"
import uvm_pkg::*;
//////////////////////////////////////////////////////////////////////
class first_v3 extends uvm_object;
    // Class properties
    rand bit [3:0] data;
    
    // Constructor
    function new(string path = "first_v3");
        super.new(path);
    endfunction
    
    // Field macros
    `uvm_object_utils_begin(first_v3)
        `uvm_field_int(data, UVM_DEFAULT)
    `uvm_object_utils_end
endclass
//////////////////////////////////////////////////////////////////////
module section3_54;
    first_v3 f1, f2;
    int status = 0;
    
    initial begin
        f1 = first_v3::type_id::create("f1");
        f2 = first_v3::type_id::create("f2");
        
        f1.randomize();
        f2.randomize();
        
        f1.print();
        f2.print();
    end
endmodule
