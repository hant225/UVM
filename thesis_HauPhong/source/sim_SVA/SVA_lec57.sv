`timescale 1ns / 1ps


module SVA_lec57;

    reg clk = 0;
    reg a = 0;
    reg b = 0;
    reg start = 0;
    
    initial begin
        #2  start = 1;
        #10 start = 0;
    end
    
    always #5 clk = ~clk;
    
    initial begin
        #10 a = 1;        
        #30 a = 0; 
        #20 a = 1;
    end 
    
    initial begin
        #24 b = 1;        
        #60 b = 0; 
    end 
    
    initial begin
        #85 $finish;
    end
    
    a1b_edge:  assert property (@(posedge clk) $rose(a) |=> b) $info("EDGE Success at %0t", $time); 
    assert property (@(posedge clk) $rose(start) |-> a[->1] ##1 b) $info("Single Success at %0t", $time);

endmodule
