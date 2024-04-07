`timescale 1ns / 1ps
//////////////////////////////////////////////////////////////////////////////////
// Company: 
// Engineer: 
// 
// Create Date: 03/13/2024 07:58:37 PM
// Design Name: 
// Module Name: sigmoid_scb
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


module sigmoid_scb;
    real x, y;
    logic [31:0] DATA_IN;
    logic [31:0] DATA_OUT;
    logic        EN;
    logic        CLK, RST;
    
    sigmoid dut(
        .clk(CLK),
        .rst(RST),
        .en(EN),
        .data_in(DATA_IN),
        .data_out(DATA_OUT)
    );
    
    initial begin
        CLK = 1'b0; RST = 1'b0; EN = 1'b0; 
        #20 RST = 1'b1;
        #188 RST = 1'b0; EN = 1'b1;
        repeat(10) begin
            #20;
            DATA_IN[31:16] = $urandom_range(0, 5);
            DATA_IN[15:0]  = $urandom();
            $display("DATA_IN = %f", $itor(DATA_IN)*(2.0**(-16.0)));
            #2000; 
            $display("DATA_OUT = %f\n", $itor(DATA_OUT)*(2.0**(-16.0)));
        end
        #200 $finish;
    end
    
    always #10 CLK = ~CLK;
    
//    initial begin
//        x = 2;
//        y = 1 / (1 + $exp(-x));
//        $display("activation input = %0.3f => activation output = %0.3f", x, y);
//    end
endmodule
