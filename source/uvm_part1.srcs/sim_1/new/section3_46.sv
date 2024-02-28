`timescale 1ns / 1ps
`include "uvm_macros.svh"
import uvm_pkg::*;
///////////////////////////////////////////////////////
class array extends uvm_object;
    // static array
    int arr1[3] = {1, 2, 3};
    
    // dynamic array
    int arr2[];
    
    // queue
    int arr3[$];
    
    // associative array
    int arr4[int];
    
    // Constructor
    function new(string path = "path");
        super.new(path);
    endfunction
    
    // Field macros
    `uvm_object_utils_begin(array)
        `uvm_field_sarray_int(arr1, UVM_DEFAULT)
        `uvm_field_array_int(arr2, UVM_DEFAULT)
        `uvm_field_queue_int(arr3, UVM_DEFAULT)
        `uvm_field_aa_int_int(arr4, UVM_DEFAULT)
    `uvm_object_utils_end
    
    // Methods
    task run();
        // Dyn array initialize
        arr2    = new[3];
        arr2[0] = 1;
        arr2[1] = 3;
        arr2[2] = 2;
        
        // Queue
        arr3.push_front(4);
        arr3.push_front(5);
        arr3.push_front(6);
        
        // Assoc arr
        arr4[0] = 7;
        arr4[3] = 7;
        arr4[5] = 9;
    endtask
endclass
///////////////////////////////////////////////////////
module section3_46;
    array a;
    initial begin
        a = new("array");
        a.run();
        a.print();
    end
endmodule
