`timescale 1ns / 1ps
//////////////////////////////////////////////////////////////////////////////////
// Company: 
// Engineer: 
// 
// Create Date: 05/04/2024 10:54:25 AM
// Design Name: 
// Module Name: test_Thuc_abs
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


module Thuc_abs#(
       parameter pDATA_WIDTH  = 32      
    )(      
      input  logic signed  [pDATA_WIDTH-1:0] data_in,
      output logic signed  [pDATA_WIDTH-1:0] abs
    );    
    assign abs = data_in[pDATA_WIDTH-1] ? {1'b0, ~data_in[pDATA_WIDTH-2:0]} : data_in;
endmodule

module test_Thuc_abs;
    logic signed [7:0] DATA_IN;
    logic signed [7:0] ABS;
    
    Thuc_abs #(.pDATA_WIDTH(8)) dut(.data_in(DATA_IN), .abs(ABS));
    
    initial begin
        repeat(100) begin
            #10 DATA_IN = $random;
            #10 $display("DATA_IN = %0d", DATA_IN);
                $display("ABS     = %0d", ABS);
                $display;
        end
    end
endmodule
