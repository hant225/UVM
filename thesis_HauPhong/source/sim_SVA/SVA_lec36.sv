`timescale 1ns / 1ps

module sva_adder(
    input clk, sample,
    input [7:0] a, b,
    output logic done,
    output [8:0] c
);

    logic [8:0] temp, tempa, tempb;
    reg [1:0] state = 0;
  
    always_ff@(posedge clk) begin
        case(state)
            0: begin 
                    if(sample == 1'b1) begin
                        tempa <= a;
                        tempb <= b;
                        done  <= 1'b0;
                        state <= 1;
                    end else begin
                        state <= 0;
                        done <= 1'b0;
                    end 
               end
            1: begin  
                    temp = tempa  + tempb;
                    done = 1'b1;
                    state <= 0;
               end
            default: begin 
                    state <= 0;
                    done <= 0;
           end
        endcase
    end  
  
    assign c = temp; 
    
endmodule

// Module with assertion
module sva_adder_assert (
    input clk, sample,
    input [7:0] a, b,
    input done,
    input [8:0] c
);

    ////////////////////Check Sum  
    RESULT_A_B: assert property  ( @(negedge clk) $rose(done) |-> (c == a + b) ) 
                    $display("[SUM] : Success Result of sum matches @ %0t",$time);
endmodule


module SVA_lec36;

    reg clk = 0;
    reg sample = 0;
    reg [7:0] a=0, b=0;
    wire [8:0] c;
    wire done;

    always #5 clk = ~clk;
    
    sva_adder dut (clk, sample, a, b, done, c);    
    sva_adder_assert dut3 (clk, sample, a, b, done, c);

    // bind adder adder_assert dut2 (clk,sample,a,b,done,c);


    //////////////////assertion
    CHECK_A_DEF: assert property (@(posedge clk) !$isunknown(a));
    CHECK_B_DEF: assert property (@(posedge clk) !$isunknown(b));
    CHECK_C_DEF: assert property (@(posedge clk) !$isunknown(c)); 

    initial begin
        $display("---------------Starting Test--------------");
        $display("Checking Result for different combination");
        @(posedge clk) {sample,a,b} = 20'h11234;
        #100;
        $display("---------------Test Complete--------------");
        $finish();
    end

    ////collectively disable multiple assertion statements
    /*initial begin
        #0  $assertoff();
        #50 $asserton();
    end*/
    
    initial begin
        #0  $assertoff(0, dut3);
        #50 $asserton();
    end

endmodule
