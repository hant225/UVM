`timescale 1ns / 1ps


module SVA_lec89;
    reg clk = 0;        
    reg rd = 0;
    reg wr = 0;
    
    always #5 clk = ~clk;
    
    initial begin
        #10 wr = 1;
        #10 wr = 0;
        #10 rd = 1;
        #40 rd = 0;
        #40 wr = 1;
        #10 wr = 0;
        #10 rd = 1;
        #60 rd = 0;
        #30 wr = 1;
        #10 wr = 0;
        #10 rd = 1;
        #20 rd = 0;
        #10 rd = 1;
        #10 rd = 0;
    end            
    
    /*A1: assert property (@(posedge clk) $rose(rd) |-> rd[*2])
            $info("A1 success at %0t", $time);*/
            
    A2: assert property (@(posedge clk) $rose(rd) |-> rd[*2:5] ##1 !rd)
            $info("A2 success at %0t", $time);                        
    
    initial begin 
        #300 $finish;
    end
endmodule