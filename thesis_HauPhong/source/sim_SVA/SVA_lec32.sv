`timescale 1ns / 1ps


module SVA_lec32;

    reg clk = 0;
    reg req = 0;
    reg ack = 0;
    
    initial begin
        #10 req = 1;
        #10 req = 0;
    end
    
    initial begin
        #0  ack = 0;
        #24 ack = 1;
    end
        
    always #5 clk = ~clk;
    
    //////////////////////////////////////////
    
    always @(posedge clk) begin
        A1: assert property (@(posedge clk) req |-> ack) 
                $info("A1 Success at %0t", $time);
            else
                $error("Fail at %0t", $time);
    end
    
    //////////////////////////////////////////
    
    initial begin
        A2: assert property (@(posedge clk) req |-> ack)
                $info("A2 Success at %0t", $time);            
    end
    
    //////////////////////////////////////////
    
    A3: assert property (@(posedge clk) req |-> ack)
            $info("A3 Success at %0t", $time);
        else
            $error("Fail at %0t", $time);
            
    //////////////////////////////////////////
    
    A4: assert property (@(posedge clk) req |-> ack) begin
            $info("A4 Success at %0t", $time);
        end else begin
            $error("Fail at %0t", $time);
        end
        
    //////////////////////////////////////////
    
    // Complex Expression
    sequence s1;
        ack;
    endsequence
            
    property p1;
        req |-> s1;
    endproperty
    
    A5: assert property (@(posedge clk) p1);
    
    //////////////////////////////////////////
    
    initial begin
        #150 $finish;
    end
    
endmodule











