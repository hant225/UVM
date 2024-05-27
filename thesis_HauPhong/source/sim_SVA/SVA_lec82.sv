`timescale 1ns / 1ps


module SVA_lec82;
    
    reg clk = 0;    
    reg req = 0;
    reg ack = 0;
    
    always #5 clk = ~clk;
    
    initial begin
        #10 req = 1;
        #10 req = 0;
        #30 req = 1;
        #10 req = 0;
        #30 req = 1;
        #10 req = 0;
        #20 req = 1;
        #10 req = 0;
    end
        
    initial begin
        #40 ack = 1;
        #10 ack = 0;
        #20 ack = 1;
        #10 ack = 0;
        #20 ack = 1;
        #10 ack = 0;
        #60 ack = 1;
        #10 ack = 0;
    end
    
    A1: assert property (@(posedge clk) req |-> ##[1:3] ack)
            $info("Success at %0t", $time);    
    
    initial begin 
        #200 $finish;
    end

endmodule
