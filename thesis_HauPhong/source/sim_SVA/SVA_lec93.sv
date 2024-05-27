`timescale 1ns / 1ps


module SVA_lec93;
    reg clk = 0;
    reg a = 0;
    reg b = 0;    
    reg temp = 0;
    
    initial begin
        #3   temp = 1;
        #113 temp = 0;
    end
        
    task write();
        #4 b = 1;
        #4 b = 0;
        #4 a = 1;
        #4 a = 0;
        #6 a = 1;
        @(posedge clk);
        #5 a = 0;
        repeat(3)  @(posedge clk);
        #9  a = 0;
        #5  a = 1;
        #10 a = 0;
        #5  a = 1;
        #10 a = 0;
        #5  b = 1;
        #10 b = 0;
    endtask
    
    always #5 clk =~clk;
    
    // check if after signal b assert, signal a assert for only non-consecutive 3 time, failure if > 3
    A1: assert property (@(posedge clk) $rose(b) |-> temp throughout a[=3] ##1 b)
            $info("Success at %0t", $time);
    
    initial begin
        #130 $finish;
    end
    
    initial begin
        write();
    end
endmodule