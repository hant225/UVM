`timescale 1ns / 1ps


module SVA_lec44;

    reg clk = 0; 
    reg a = 0;
    reg b = 0;    
    
    initial begin
        #120 $finish;
    end
        
    always #5 clk = ~clk;
    
    sequence s1;
        a ##1 b;
    endsequence
        
    property p1;
        s1 |-> b;
    endproperty
        
    assert property (@(posedge clk) p1)
        $info("Success at %0t", $time);
    
endmodule
