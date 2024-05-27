`timescale 1ns / 1ps


module SVA_lec70;
    reg clk = 0;
    reg [3:0] a = 4'b0000;
    reg req = 0;
    reg ack = 0;
    reg en  = 0;

        
    always #5 clk = ~clk;
    
    initial begin
        #10 req = 1;
        #30 req = 0;
    end        
    
    initial begin
        #24 ack = 1;
        #40 ack = 0;
    end
    
    initial begin
        #5
        for(int i = 0; i < 16; i++) begin
            a = i;
            #10;
        end
    end
    
    initial begin
        #10 en = 1;
        #60 en = 0;
    end
    
    A1: assert property (@(posedge clk) $rose(req) |=> $rose(ack)) 
            $info("Success at %0t", $time);

    /*A2: assert property (@(posedge clk) $rose(en) |=> (a == $past(a + 1))) 
            $info("Success at %0t", $time);*/

    A2: assert property (@(posedge clk) disable iff(!en) en |=> (a == $past(a + 1))) 
            $info("Success at %0t", $time);

    initial begin
        #150 $finish;
    end

endmodule
