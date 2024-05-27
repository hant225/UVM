`timescale 1ns / 1ps

module SVA_lec80;

    reg clk = 0;
    
    reg req = 0;
    reg ack = 0;
    
    always #5 clk = ~clk;
    
    initial begin
        #10 req = 1;
        #20 req = 0;
        #10;
    end
    
    
    initial begin
        #50 ack = 1;
        #10 ack = 0;
        #10;
    end
    
    A1: assert property (@(posedge clk) req |-> ##4 ack)
            $info("Success at %0t", $time);
    
    initial begin 
        #80 $finish;
    end

endmodule
