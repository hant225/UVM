`timescale 1ns / 1ps
//////////////////////////////////////////////////////////////////////////////////
// Company: 
// Engineer: 
// 
// Create Date: 04/04/2024 08:25:54 PM
// Design Name: 
// Module Name: test_shift
// Project Name: 
// Target Devices: 
// Tool Versions: 
// Description: 
// 
// Dependencies: 
// 
// Revision:
// Revision 0.01 - File Created
// Additional Comments:
// 
//////////////////////////////////////////////////////////////////////////////////


module test_shift;
    logic [31:0] A;
    logic [31:0] result;
    logic [31:0] A_sub;
    logic [31:0] B;

    bit do_shift_right;     // 1 : shift right | 0 : shift left
    int shift_amount;
    
    import "DPI-C" function void c_shift(input logic [31:0] B);
    import "DPI-C" function void func_for_test(input logic [15:0] A, output logic [31:0] A_sub);
    import "DPI-C" function void do_shift(input logic [31:0] A, 
                                          input bit do_shift_right, 
                                          input int shift_amount,
                                          output logic [31:0] result
                                          );

    initial begin
        A = -200000;
        do_shift(A, 0, 8, result);
    end


//    initial begin
//        B = -100000;
//        $display("[SV-BIN] B = %0d", $signed(B));         
//        c_shift(B);
//    end

//    initial begin
//        A = 16'b1011_1010_1110_0011;
//        func_for_test(A, A_sub);
//        $display("[SV] sub_A = %0b", A_sub);
//    end
endmodule
