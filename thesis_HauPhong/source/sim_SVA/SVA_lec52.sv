`timescale 1ns / 1ps


module SVA_lec52;

    reg clk = 0;
    reg req = 0;
    reg ack = 0;
    
    task req_stimuli(); 
        #10 req = 1;
        #10 req = 0;
        #10 req = 1;
        #10 req = 0;
        #10 req = 1;
        #10 req = 0; 
    
    endtask
        
    task ack_stimuli(); 
        #10 ack = 1;
        #10 ack = 0;
        #10 ack = 0;
        #10 ack = 0;
        #10 ack = 0;
        #10 ack = 1;
        #10 ack = 0;
    endtask
    
    initial begin
        #0  req_stimuli();
        #20 req_stimuli();
    end
    
    initial begin
        #0  ack_stimuli();  
        #20 ack_stimuli();
    end
    
    always #5 clk = ~clk;
    
    
    /*A1: assert property (@(posedge clk) req |-> ack)
            $info("Overlapping success at %0t", $time);
        else
            $error("Overlapping failure at %0t", $time);*/
    A1: assert property (@(posedge clk) req |=> ack)
            $info("Non-Overlapping success at %0t", $time);
        else
            $error("Non-Overlapping failure at %0t", $time);            
    
    
    initial begin
        #200 $finish;
    end
     
endmodule
