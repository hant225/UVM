`timescale 1ns / 1ps
//////////////////////////////////////////////////////////////////////////////////
// Company: 
// Engineer: 
// 
// Create Date: 03/17/2024 12:07:54 PM
// Design Name: 
// Module Name: dequantize_test
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


module dequantize_test;
    reg CLK, RST;
    reg EN;
    reg signed [31:0] DATA_IN;
    reg signed [31:0] SCALE;
    wire signed [31:0] DATA_OUT;

    
    dequantize DUT(
      .clk(CLK),
      .en(EN),
      .rst(RST),
      .data_in(DATA_IN),
      .scale(SCALE),
      .data_out(DATA_OUT)
    );
    
    initial begin
        CLK = 1'b0; RST = 1'b1; EN = 1'b0; DATA_IN = 32'd0; SCALE = 32'd0;
        #145 RST = 1'b0;
        
        for(int i = 0; i < 20; i++) begin
            #20 DATA_IN = $urandom_range(-1000, 500);
                SCALE   = $urandom_range(-200, 2000); 
                EN = 1'b1;
            #200;
            if(DATA_OUT == DATA_IN * SCALE) 
                $display("PASSED");
            else
                $display("FAILED");
            
            
            $display("data_in  : %d", DATA_IN);
            $display("scale    : %d", SCALE);
            $display("real data_out     : %d", DATA_OUT);
            $display("expected data_out : %d", DATA_IN * SCALE);
        end
        #200 $finish;
    end
    always #10 CLK = ~CLK;
    
    
endmodule
