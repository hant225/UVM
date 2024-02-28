`timescale 1ns / 1ps
`include "uvm_macros.svh"
import uvm_pkg::*;
/////////////////////////////////////////////////////////////////////////////
module section4_70;
    comp c;

//    initial begin
//        run_test("comp");
//    end

    initial begin
        c = comp::type_id::create("c", null);
        c.build_phase(null);
    end
endmodule
