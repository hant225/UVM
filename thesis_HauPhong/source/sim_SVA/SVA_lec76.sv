`timescale 1ns / 1ps

module SVA_lec76;
    
    reg [3:0] a = 4'b0000;
    
    reg clk = 0;
    reg en = 0;
    
    
    reg req = 0;
    reg ack = 0;
    
    initial begin  
        #10 req = 1;
        #30 req = 0;
        #50 req = 1;
        #10 req = 0;
    end
        
    initial begin
        #0  ack = 0;
        #24 ack = 1;
        #40 ack = 0;
        #60 ack = 1;
        #10 ack = 0;
    end

    always #5 clk = ~clk;
    
    initial begin
        #10;
        for(int i = 0; i< 15; i++) begin
            a = a+1;
            @(posedge clk);
        end
    end
    
    initial begin
        #10 en = 1;
        #60 en = 0;        
    end
        
    initial begin
        #150 $finish;
    end
    
    // check if ack followed by req
    req_1_ack: assert property (@(posedge clk) $rose(req) |=> $rose(ack))
                    $info("req followed by ack @ %0t", $time);
    
    // when en assert check if a increase each clock
    a_en: assert property (@(posedge clk) disable iff (!en) en |-> (a == $past(a + 1)))
                    $info("a valid at @ %0t", $time); 
endmodule












