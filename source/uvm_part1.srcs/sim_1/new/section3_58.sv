`timescale 1ns / 1ps
`include "uvm_macros.svh"
import uvm_pkg::*; 
//////////////////////////////////////////////////////////////////////////////////

class first_v4 extends uvm_object;
    // Class properties
    rand bit [3:0] data;
    
    // Constructor
    function new(string path = "first_v4");
        super.new(path);
    endfunction
    
    // Field macros
    `uvm_object_utils_begin(first_v4)
        `uvm_field_int(data, UVM_DEFAULT)
    `uvm_object_utils_end
endclass

//////////////////////////////////////////////////////////////////////////////////

class first_v4_mod extends first_v4;
    // Class properties
    rand bit ack;
    
    // Constructor
    function new(string path = "first_v4_mod");
        super.new(path);
    endfunction
    
    // Field macros
    `uvm_object_utils_begin(first_v4_mod)
        `uvm_field_int(ack, UVM_DEFAULT)
    `uvm_object_utils_end
endclass

//////////////////////////////////////////////////////////////////////////////////

class comp extends uvm_component;
    `uvm_component_utils(comp)
    
    // Class properties
    first_v4 f;
    
    // Constructor
    function new(string path = "second", uvm_component parent = null);
        super.new(path, parent);
        f = first_v4::type_id::create("f");
        f.randomize();
        f.print();
    endfunction
endclass

//////////////////////////////////////////////////////////////////////////////////
module section3_58;
    comp c;
    
    initial begin
        c.set_type_override_by_type(first_v4::get_type, first_v4_mod::get_type);
        c = comp::type_id::create("comp", null);
    end
endmodule
