`timescale 1ns / 1ps
`include "uvm_macros.svh"
import uvm_pkg::*;
//////////////////////////////////////////////////////////////////////

class first_v2 extends uvm_object;
    // Class properties
    rand bit [3:0] data;
    // Constructor
    function new(string path = "first_v2");
        super.new(path);
    endfunction
    // Field macros
    `uvm_object_utils_begin(first_v2)
        `uvm_field_int(data, UVM_DEFAULT);
    `uvm_object_utils_end
endclass

//////////////////////////////////////////////////////////////////////

class second extends uvm_object;
    // Class properties
    first_v2 f;
    // Constructor
    function new(string path = "second");
        super.new(path);
        f = new("first_v2");
    endfunction
    // Field macros
    `uvm_object_utils_begin(second)
        `uvm_field_object(f, UVM_DEFAULT)
    `uvm_object_utils_end
endclass

//////////////////////////////////////////////////////////////////////

module section3_50;
    second s1, s2;
    
    initial begin    
//        // shallow copy
//        `uvm_info("TOP_TB", "SHALLOW COPY", UVM_NONE)
//        s1 = new("s1");
//        s1.f.randomize();
        
//        s2 = s1;
//        s1.print();
//        s2.print();
        
//        s1.f.randomize();
//        s1.print();
//        s2.print();
        
        // deep copy
        s1 = new("s1");
        s2 = new("s2");
        
        s1.f.randomize();
        
        s2.copy(s1);
        
        s1.print();
        s2.print();
        
        s1.f.randomize();
        s1.print();
        s2.print();
    end
endmodule
