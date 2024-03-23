`timescale 1ns / 1ps
//////////////////////////////////////////////////////////////////////////////////
// Company: 
// Engineer: 
// 
// Create Date: 03/19/2024 08:25:40 PM
// Design Name: 
// Module Name: bias_tb
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


module bias_tb;
    reg           CLK, RST;
    reg           WR_EN;
    reg  [31:0]   WEIGHT_ADDR;
    reg  [63:0]   WEIGHT_DATA;
    reg  [3:0]    BIAS_ADDR;
    wire [1023:0] BIAS_DATA;
    

    bias_ram #(
      .pWEIGHT_DATA_WIDTH(64           ),
      .pWEIGHT_BASE_ADDR (32'h4000_0000),
      .pBIAS_NUM         (16           ),
      .pBLOCK_RAM_NUM    (16           )
    ) DUT (
      .clk(CLK),
      .rst(RST),
      .wr_en(WR_EN),
      .weight_addr(WEIGHT_ADDR),
      .weight_data(WEIGHT_DATA),
      .bias_addr(BIAS_ADDR),
      .bias_data(BIAS_DATA)
    );
    
    initial begin
        CLK = 0; RST = 0; WR_EN = 0;
        #145 RST = 1'b1;
        #200 RST = 1'b0;
        for(int i = 1073741824; i < 1073741824 + 10000; i++) begin
            #20 WR_EN = 1;
                WEIGHT_ADDR = i;  
                WEIGHT_DATA = $urandom(); 
        end
        
        #20 WR_EN = 0;
        for(int i = 0; i < 16; i++) begin
            #20 BIAS_ADDR = i;
        end
        #2000 $finish;
    end
    
    initial begin
        $monitor("BIAS_ADDR=%0h", BIAS_DATA);
    end
    
    always #10 CLK = ~CLK;
endmodule
