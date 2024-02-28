`timescale 1ns / 1ps
`include "uvm_macros.svh"
import uvm_pkg::*;
////////////////////////////////////////////////////////////////
class parent extends uvm_object;
    // Constructor
    function new(string path = "parent");
        super.new(path);
    endfunction
    
    // Class properties
    rand bit [3:0] data;
    
    // Field macros
    `uvm_object_utils_begin(parent)
        `uvm_field_int(data, UVM_DEFAULT)
    `uvm_object_utils_end
endclass
////////////////////////////////////////////////////////////////
class child extends uvm_object;
    // Declare handle of parent class
    parent p;
    
    // Constructor
    function new(string path = "child");
        super.new(path);
        p = new("parent");      // build_phase + create
    endfunction
    
    // Field macros
    `uvm_object_utils_begin(child)
        `uvm_field_object(p, UVM_DEFAULT)
    `uvm_object_utils_end
endclass
////////////////////////////////////////////////////////////////
module section3_44;
    child c;
    
    initial begin
        c = new("child");
        c.p.randomize();
        c.print();
    end
endmodule
