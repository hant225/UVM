`timescale 1ns / 1ps


module SVA_lec61;

    reg a = 1, clk = 0;
            
    always #5 clk = ~clk;    
    always #5 a = ~a;

    always@(posedge clk) begin
        $info("Value of a : %0b and $sampled(a) : %0b", a, $sampled(a));
    end

    assert property (@(posedge clk) a) $info("Value a : %0b", $sampled(a));

    initial begin
        #120 $finish;
    end        
    
endmodule
