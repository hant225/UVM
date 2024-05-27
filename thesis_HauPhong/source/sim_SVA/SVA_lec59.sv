`timescale 1ns / 1ps


module SVA_lec59;
    reg a = 0;
    reg b = 0; 
    reg clk = 0;
    
    initial begin  
        #10 a = 1;
        #30 a = 0;
    end
    
    
    initial begin
        #0  b = 0;
        #24 b = 1;
        #40 b = 0;
    end
    
    always #5 clk = ~clk;

    initial begin
        #85 $finish;
    end

    A1: assert property (@(posedge clk) $rose(a) |=> $rose(b)) $info("Success at %0t", $time);

endmodule
