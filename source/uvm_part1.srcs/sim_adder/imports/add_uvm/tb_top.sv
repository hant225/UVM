`timescale 1ns / 1ps
`include "uvm_macros.svh"
import uvm_pkg::*;
`include "test.sv"

//////////////////////////////////////////////////////////////////////////////////

module tb_top;
    add_if aif();
    adder DUT(.a(aif.a), .b(aif.b), .y(aif.y));
    
    initial begin
        uvm_config_db#(virtual add_if)::set(null, "uvm_test_top.e.a*", "aif", aif);
        run_test("test");
    end
endmodule
