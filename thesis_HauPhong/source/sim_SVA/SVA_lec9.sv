`timescale 1ns / 1ps


module sub_module(
    input wire a, 
    input wire b,
    input wire s,
    output reg y
);

    always @(*) begin
        if(s == 1'b1)
            y <= a;
        else 
            y <= b;    
    end        
endmodule

module top(
    input wire ta, 
    input wire tb,
    input wire ts,
    output reg ty,
    output reg tmp
);
    sub_module sub_inst(.a(ta), .b(tb), .s(ts), .y(ty));
    assign tmp = 1'b0;
endmodule

module sva_dummy(
    input logic a, 
    input logic b,
    input logic s,
    output logic y    
);
    
    assert property (@(s) y == 1) $info("Success"); //else $info("*****************************************%0b", $sampled(y));
endmodule

module bind_tb;
    reg TA;
    reg TB;
    reg TS;
    wire TY;
    wire TMP;
    wire sub_s;       
    
    // Binding solution
    top DUT(.ta(TA), .tb(TB), .ts(TS), .ty(TY), .tmp(TMP));
    bind sub_module : top.sub_inst sva_dummy sva (.*);
    // Assign solution
    assign sub_s = DUT.sub_inst.s;
        
    initial begin
        #0  TA = 0 ; TB = 0; TS = 0;
        #10 TA = 0 ; TB = 0; TS = 1;
        #10 TA = 0 ; TB = 1; TS = 0;
        #10 TA = 0 ; TB = 1; TS = 1;
        #10 TA = 1 ; TB = 0; TS = 0;
        #10 TA = 1 ; TB = 0; TS = 1;
        #10 TA = 1 ; TB = 1; TS = 0;
        #10 TA = 1 ; TB = 1; TS = 1;
        #10 $finish;
    end
    
endmodule