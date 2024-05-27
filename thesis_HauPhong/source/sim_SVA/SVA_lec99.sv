`timescale 1ns / 1ps


module SVA_lec99;

    reg clk = 0;
    reg rst = 0;
    reg ce  = 0;
    
    always #5 clk = ~clk;        
    
    initial begin
        #0  rst = 0;
        #20 ce = 1;
            rst = 0;
        #20 ce = 0;
            rst = 1;
        #20 rst= 0;
        #4  rst = 1;
        #10 rst = 0;
    end
    
    // After rst high in 2 non consecutive clk, next
    // clk tick rst will assert high
    A1: assert property (@(posedge clk) $rose(rst) |-> rst[->2] ##1 rst)
            $info("Success at %0t", $time);
    
    initial begin       
        #120 $finish;
    end            

endmodule
