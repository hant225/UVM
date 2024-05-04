`timescale 1ns / 1ps
//////////////////////////////////////////////////////////////////////////////////
// Company: 
// Engineer: 
// 
// Create Date: 05/01/2024 04:54:19 PM
// Design Name: 
// Module Name: test_wait
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


module test_wait;
    logic clk1, clk2;
    int count;
    initial begin
        count = 0; clk1 = 0; clk2 = 0;
        forever begin
            if(count == 10)
                $finish;
            @(posedge clk1 or posedge clk2);
            $display("[%0t] positive edge detected", $time);
            count++;
        end
    end
    
    always #10 clk1 = ~clk1;
    always #18 clk2 = ~clk2;        
endmodule
