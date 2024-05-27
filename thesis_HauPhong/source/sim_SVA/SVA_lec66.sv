`timescale 1ns / 1ps


module SVA_lec66;
    
    reg clk = 0;
    reg a;    
    reg [3:0] b;
    wire c;
        
    always #5 clk = ~clk;
    
    //always #2 en = ~en;
    
    initial begin       
        #10 a = 0;
        #20 a = 1;
        #20 a = 0;
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
        $info("Value of a : %0b and $fell(a)", $sampled(a), $fell(a));
    end

endmodule
