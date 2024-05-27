`timescale 1ns / 1ps


module SVA_lec87;
    reg clk = 0;    
    reg rd = 0;
    reg wr = 0;
    
    always #5 clk = ~clk;
    
    initial begin
        #10 wr = 1;
        #10 wr = 0;
        #10 rd = 1;
        #20 rd = 0;
        #40 wr = 1;
        #10 wr = 0;
        #10 rd = 1;
        #20 rd = 0;
        #30 wr = 1;
        #10 wr = 0;
        #10 rd = 1;
        #10 rd = 0;
    end
    
    // wr --> antecedent
    // check if after wr, after 2 cycles rd request assert and stay high for 2 consecutive cycles
    /*A1: assert property (@(posedge clk) $rose(wr) |-> ##2 rd[*2])
            $info("Success at %0t", $time);*/
    
    // check if rd always remains high for 2 cycles whenever it rises
    A2: assert property (@(posedge clk) $rose(rd) |-> rd[*2])
            $info("Success at %0t", $time);
    
    initial begin 
        #220 $finish;
    end
endmodule