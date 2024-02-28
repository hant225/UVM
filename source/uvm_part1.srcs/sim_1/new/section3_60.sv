`timescale 1ns / 1ps
`include "uvm_macros.svh"
import uvm_pkg::*;
//////////////////////////////////////////////////////////////////////////////////
 
class obj_2 extends uvm_object;
    `uvm_object_utils(obj_2)
    
    // Constructor
    function new(string path = "OBJ_2");
        super.new(path);
    endfunction
    
    // Properties
    bit [3:0] a = 4;
    string b = "UVM";
    real c = 12.34;
    bit printall = 1;
    
    
    // do_print method
    virtual function void do_print(uvm_printer printer);
        super.do_print(printer);
        if(printall) begin
            printer.print_field_int("a", a, $bits(a), UVM_HEX);
            printer.print_string("b", b);
            printer.print_real("c", c);
            printer.print_field_int("d", d, $bits(d), UVM_HEX);
            printer.print_field_int("e", e, $bits(e), UVM_HEX);
        end else begin
            printer.print_field_int("d", d, $bits(d), UVM_HEX);
            printer.print_field_int("e", e, $bits(e), UVM_HEX);
        end
    endfunction
    
    // convert2string method
    virtual function string convert2string();
        string s = super.convert2string;
        s = {s, $sformatf("a : %0d", a)};
        s = {s, $sformatf("b : %0s", b)};
        s = {s, $sformatf("c : %0f", c)};
        return s;
    endfunction
    
    // do_copy method
    rand bit [3:0] d;
    rand bit [3:0] e;
    
    virtual function void do_copy(uvm_object rhs);
        obj_2 temp;
        $cast(temp, rhs);
        super.do_copy(rhs);
        
        this.d = temp.d;
        this.e = temp.e;    
    endfunction
    
    // do_compare method
    virtual function bit do_compare(uvm_object rhs, uvm_comparer comparer);
        obj_2 temp;
        int status;
        $cast(temp, rhs);
        status = super.do_compare(rhs, comparer) && (d == temp.d) && (e == temp.e);
        return status;
    endfunction
endclass
 
//////////////////////////////////////////////////////////////////////////////////
module section3_60;
    obj_2 o;
    obj_2 o1, o2;
    int status;
    initial begin
        o  = obj_2::type_id::create("o");
        o1 = obj_2::type_id::create("o1");
        o2 = obj_2::type_id::create("o2");
        /*o.print();
        `uvm_info("TB_TOP", $sformatf("%0s", o.convert2string), UVM_NONE)
        
        o1.randomize();
        o1.print();
        o2.copy(o1);
    
        `uvm_info("TB_TOP", "----------------------- PRINT ALL -----------------------", UVM_NONE)
        o2.print();
        
        `uvm_info("TB_TOP", "----------------------- PRINT SELECTED -----------------------", UVM_NONE)
        o2.printall = 0;
        o2.print();*/
        
        o1.randomize();
        o1.print();
        o2.copy(o1);
        status = o2.compare(o1);
        $display("status : %0d", status); 
    end
endmodule
