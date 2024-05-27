`timescale 1ns / 1ps

module SVA_lec7;
    reg clk = 0;
    reg start = 0;
    integer i = 0;
    integer count = 0;
    reg temp = 0;
    
    initial begin
        #2   temp = 1;
        #200 temp = 0;
    end
    
    initial begin
        #80 start = 1;
        #10 start = 0;
    end    
    
    always #5 clk = ~clk;
    

    
    /*always @(posedge clk) begin
        if(start == 1'b1)
            $display("Verilog Success at %0t", $time);
        else    
            $error("Verilog Failure at %0t", $time);
    end*/
    
    // VERILOG -----------------------------    
    task check();
        for(i = 0; i < 20; i++) begin
            @(posedge clk);
            if(start == 1'b1) 
                count++;
        end
    endtask
    
    
    initial begin
        check();
        if(count > 0)    
            $display("[Verilog] Success at %0t", $time);
        else    
            $error("[Verilog] Failure at %0t", $time);
    end
    
    // ASSERTION -----------------------------
    A1: assert property (@(posedge clk) $rose(temp) |-> temp throughout start[->1]) $info("[SVA] Success at %0t", $time);
    
    initial begin
        #210 $finish;
    end
endmodule
