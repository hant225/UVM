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
  parameter pDATA_WIDTH  = 32;
  parameter pFRAC_NUM    = 16;
  logic signed [pDATA_WIDTH-1:0] FLOAT_2_375   = {{pDATA_WIDTH-6{1'b0}}, 6'b10_011}  << (pFRAC_NUM-3);
  logic signed [pDATA_WIDTH-1:0] FLOAT_0_84375 = {{pDATA_WIDTH-7{1'b0}}, 7'b0_11011} << (pFRAC_NUM-5);
  logic signed [pDATA_WIDTH-1:0] FLOAT_0_625   = {{pDATA_WIDTH-4{1'b0}}, 4'b0_101}   << (pFRAC_NUM-3);
  logic signed [pDATA_WIDTH-1:0] FLOAT_0_5     = {{pDATA_WIDTH-2{1'b0}}, 2'b0_1}     << (pFRAC_NUM-1);
  
  initial begin
    $display("%b || %f", FLOAT_2_375, $itor(FLOAT_2_375)     * (2.0**(-16.0)) );
    $display("%b || %f", FLOAT_0_84375, $itor(FLOAT_0_84375) * (2.0**(-16.0)) );
    $display("%b || %f", FLOAT_0_625, $itor(FLOAT_0_625)     * (2.0**(-16.0)) );
    $display("%b || %f", FLOAT_0_5, $itor(FLOAT_0_5)         * (2.0**(-16.0)) );
    $finish;
  end
endmodule
