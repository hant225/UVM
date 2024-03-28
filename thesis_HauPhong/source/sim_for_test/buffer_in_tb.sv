`timescale 1ns / 1ps
//////////////////////////////////////////////////////////////////////////////////
// Company: 
// Engineer: 
// 
// Create Date: 03/26/2024 10:22:05 PM
// Design Name: 
// Module Name: buffer_in_tb
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


module buffer_in_tb;
    logic CLK, RST;
    logic        EN;
    logic [3:0]  PIXEL;
    logic [71:0] DATA_IN;
    logic [7:0]  DATA_OUT;
    logic        VALID;

    pe_conv_mac_buffer_in_conv1 #(
      .pDATA_WIDTH    (8),
      .pKERNEL_SIZE   (3),
      .pINPUT_CHANNEL (1),
      .pINPUT_PARALLEL(1)
    ) DUT (
      .clk(CLK),
      .rst(RST),
      .en(EN),
      .pixel(PIXEL),
      .data_in(DATA_IN),
      .data_out(DATA_OUT),
      .valid(VALID)
    );

    initial begin
        CLK = 1'b0; RST = 1'b0; 
        PIXEL = 4'd0; DATA_IN = $urandom();
        EN = 1'b0;
        #250 RST = 1'b1;
        #200 RST = 1'b0;
        #100 EN = 1'b1;
        #20  EN = 1'b0;
        #13;
        #40  for(int i = 0; i < 10; i++) begin
                #20 PIXEL = $urandom_range(0,8);
             end
        #20 EN = 1'b1;
            for(int i = 0; i < 10; i++) begin
                #20 DATA_IN = $urandom();
            end
        #20 $finish;
    end
    
    always #10 CLK = ~CLK;
endmodule
