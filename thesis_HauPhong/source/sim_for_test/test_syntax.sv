`timescale 1ns / 1ps
//////////////////////////////////////////////////////////////////////////////////
// Company: 
// Engineer: 
// 
// Create Date: 03/28/2024 02:22:53 PM
// Design Name: 
// Module Name: test_syntax
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


module test_syntax;
    logic valid;
    logic a;
    logic b;
    initial begin
        assign a = 1;
        assign b = 1;
        assign valid = a && b == 0;
    end
endmodule
