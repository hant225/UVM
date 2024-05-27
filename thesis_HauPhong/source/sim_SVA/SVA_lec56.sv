`timescale 1ns / 1ps


module SVA_lec56;

    reg clk = 0;
    reg a = 0;
    reg b = 0;
    
    always #5 clk = ~clk;
    
    initial begin
        #10 a = 1;        
        #30 a = 0; 
    end 
    
    initial begin
        #24 b = 1;        
        #40 b = 0; 
    end 
    
    initial begin
        #85 $finish;
    end
    
    a1b_level: assert property (@(posedge clk) a|=> b) 
                    $info("Success at %0t", $time);
    /*a1b_edge:  assert property (@(posedge clk) $rose(a) |=> b)
                    $info("Success at %0t", $time); */


endmodule
