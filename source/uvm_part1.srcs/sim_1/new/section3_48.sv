`timescale 1ns / 1ps
`include "uvm_macros.svh"
import uvm_pkg::*;
//////////////////////////////////////////////////////////////////////////////////
class first extends uvm_object;
    // Class properties
    rand bit[3:0] data;
    
    // Constructor
    function new(string path = "first");
        super.new(path);
    endfunction
    
    // Field macro
    `uvm_object_utils_begin(first)
        `uvm_field_int(data, UVM_DEFAULT)
    `uvm_object_utils_end
endclass
//////////////////////////////////////////////////////////////////////////////////
module section3_48;
    first f;
    first s;
    
    // COPY
    /*initial begin
        f = new("first");
        s = new("second");
        f.randomize();
        s.copy(f);
        f.print();
        s.print();
    end*/
    
    // CLONE
    initial begin
        f = new("first");
        f.randomize();
        $cast(s, f.clone());
//        s = f.clone();        // Syntax error
        f.print();
        s.print();
    end 
endmodule

