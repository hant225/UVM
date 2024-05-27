`timescale 1ns / 1ps


module SVA_lec95;
    reg clk = 0;
    reg a = 0;
    reg b = 0;
    
    task write();
        #4 b = 1;
        #4 b = 0;
        #4 a = 1;
        #4 a = 0;
        #6 a = 1;
        @(posedge clk);
        #5 a = 0;
        repeat(3)  @(posedge clk);
        #9  a = 1;
        #5  a = 0;
        #10 a = 0;
        #5  a = 1;
        #10 a = 0;
        #5  b = 1;
        #10 b = 0;
    endtask
    
    always #5 clk =~clk;        
    
    
    initial begin
        #120 $finish;
    end
    
    A1: assert property (@(posedge clk) $rose(b) |-> a[=2:3] ##1 b)
            $info("A1 Success at %0t", $time);
            
    A2: assert property (@(posedge clk) $rose(b) |-> a[=2])
            $info("A2 Success at %0t", $time);                    
    
    initial begin
        write();
    end
endmodule