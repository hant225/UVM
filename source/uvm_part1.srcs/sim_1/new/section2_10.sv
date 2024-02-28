`timescale 1ns / 1ps
`include "uvm_macros.svh"
import uvm_pkg::*;


module section2_10;
    initial begin
        #50
        `uvm_info("TB_TOP", "HELLO WORLD!", UVM_LOW);
        $display("HELLO WORLD! with display");
    end
endmodule
