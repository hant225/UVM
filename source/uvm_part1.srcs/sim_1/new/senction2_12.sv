`timescale 1ns / 1ps
`include "uvm_macros.svh"
import uvm_pkg::*;

module senction2_12;
    int data = 56;
    
    initial begin
        `uvm_info("TB_TOP", $sformatf("value of variable: %0d", data), UVM_NONE);  
    end
endmodule
