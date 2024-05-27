`timescale 1ns / 1ps


module SVA_lec63;

    reg clk = 0;
    reg a ;    
    reg [3:0] b;
    wire c;

    always #5 clk = ~clk;

    initial begin        
        #10 a = 0;
        #20 a = 1;
        #20 a = 0;
        #10 a = 1;
        #20 a = 0;
        #10 a = 1;
    end    
    
    initial begin
        #0  b = 4'b0100;
        #10 b = 4'b0101;
        #10 b = 4'b0100;
        #10 b = 4'b0101;
        #10 b = 4'b0100;
        #10 b = 4'b0101;
        #10 b = 4'b0000; 
    end
        
    initial begin
        #120 $finish;
    end
        
    always @(posedge clk) begin
        $info("Value of a : %0b and $rose(a) : %0b", $sampled(a), $rose(a));
        // $info("Value of b : %b and $rose(b) : %b", $sampled(b), $rose(b));
    end    

endmodule











