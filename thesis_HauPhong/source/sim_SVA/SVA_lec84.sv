`timescale 1ns / 1ps

module SVA_lec84;

    reg clk = 0;    
    reg req = 0;
    reg ack = 0;
        
    reg temp = 0;
    reg done = 0;
    
    initial begin
        #3   temp = 1;
        #198 temp = 0;
    end
    
    initial begin
        #200 done = 1;
        #10  done = 0;
    end
    
    
    always #5 clk = ~clk;
    
    initial begin
        #10 req = 1;
        #10 req = 0;        
    end
    
    
    initial begin
        #120 ack = 0;
        #10  ack = 0;
    end
    
    // Short cuts
    // ##[0:$] = ##[*]
    // ##[1:$] = ##[+]
    
    /*A1: assert property (@(posedge clk) req |-> ##[1:$] ack)
            $info("Success at %0t", $time);*/        
    
    A2: assert property (@(posedge clk) req |-> temp throughout (##[1:$] ack))
            $info("Success at %0t", $time);
            
    A3: assert property (@(posedge clk) req |-> (##[1:$] ack) within done[->1])
            $info("Success at %0t", $time);                        
    
    initial begin 
        #210 $finish;
    end
endmodule


