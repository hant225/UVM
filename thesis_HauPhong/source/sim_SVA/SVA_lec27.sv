`timescale 1ns / 1ps


module SVA_lec27;

    reg clk = 0;
    reg a = 0;
    reg b = 0;
    wire c = 0;
    
    
    always #5 clk = ~clk; ///generation of clock signal    
    always #7 a = ~a; ///generation of a    
    always #8 b = ~b; ///generation of b

    always@(posedge clk) begin   
        A1 : assert (a == b) begin
                $info("Success at %0t",$time);  
             end else begin
                $error("Fail at %0t",$time);
             end
    end
    
    initial begin 
        #150 $finish;
    end
endmodule
