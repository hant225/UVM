`timescale 1ns / 1ps

//////////////////////////////////////////////////////////////////////////////////

module SVA_lec5;

    reg clk = 0;
    reg a = 0;
    reg b = 0;
    
    task a_b();
        #10 a = 1;
        #10 a = 0;
        #30 b = 1;
        #10 b = 0;
        #50 a = 1;
        #10 a = 0;
        #30 b = 1;
        #10 b = 0;
    endtask
    
    always #5 clk =~clk;
    
    initial begin
        #200;
        $finish;
    end
    
    initial begin
        a_b();
    end
    
    default clocking
        @(posedge clk);
    endclocking

    always @(posedge clk) begin
        if(a == 1'b1) begin
            repeat(4) @(posedge clk);
            if(b == 1'b1)
                $display("Success method 1 : Verilog at %0t", $time);
            else
                $error("b does not arrive at time");
        end
    end

    assert property ( a |-> ##4 b) $info("Success method 2 : SVA at %0t", $time);

endmodule
