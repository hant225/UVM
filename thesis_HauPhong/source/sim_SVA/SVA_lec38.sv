`timescale 1ns / 1ps


module SVA_lec38;
    
    reg clk = 0;
    reg rst = 0;
    reg a = 0;
    
    always #5 clk = ~clk;
    always #10 a = ~a;
    
    initial begin
        #5  rst = 1;
        #50 rst = 0;
    end
    
    initial begin
        #150 $finish();
    end

    CHECK_A: assert property (@(posedge clk) $rose(a))
                $info("Valid A value");
                
    initial begin
        @(posedge rst) $assertoff();
        @(negedge rst) $asserton();
    end
                    
endmodule
