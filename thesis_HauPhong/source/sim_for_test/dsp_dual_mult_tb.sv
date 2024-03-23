`timescale 1ns / 1ps

//////////////////////////////////////////////////////////////////////////////////

module dsp_dual_mult_tb;
    logic CLK, RST, EN;
    logic signed [7:0]  A;
    logic signed [7:0]  B;
    logic        [7:0]  C;
    logic signed [15:0] AC;
    logic signed [15:0] BC;
    logic               VALID_OUT;

    int pass_count = 0;
    int fail_count = 0;
    logic signed [15:0] se_A;
    logic signed [15:0] se_B;
    logic signed [15:0] se_C;
    logic signed [31:0] se_result_AC;
    logic signed [31:0] se_result_BC;
    logic signed [15:0] expected_ac;
    logic signed [15:0] expected_bc;
    
    dsp_dual_mult DUT(
      .clk(CLK),
      .rst(RST),
      .en(EN),
      .a(A),
      .b(B),
      .c(C),
      .ac(AC),
      .bc(BC),
      .valid_out(VALID_OUT)
    );
    
    initial begin
        CLK = 1'b0; RST = 1'b0; EN = 1'b0;
        #125 RST = 1'b1;
        #100 RST = 1'b0;       
        
        for(int i = 0; i < 1000; i++) begin
            #20 EN = 1'b1;
                A = $random();
                B = $random();
                C = $random();
                
            // get reliable result
            se_A = A;
            se_B = B;
            se_C = C;
            se_result_AC = se_A * se_C;
            se_result_BC = se_B * se_C;
            expected_ac = se_result_AC[15:0];
            expected_bc = se_result_BC[15:0];

      
            // wait for result valid
            @(posedge VALID_OUT);
            repeat(2) @(posedge CLK);          
            if(AC == expected_ac && BC == expected_bc) begin
                $display("PASSED");
                pass_count++;
            end else begin    
                $display("ERROR");
                fail_count++;
            end
        
            // display            
            $display("A           = %0d", A);
            $display("B           = %0d", B);
            $display("C           = %0d", $unsigned(C));
            $display("Expected AC = %0d", expected_ac);
            $display("Expected BC = %0d", expected_bc);
            $display("Real AC     = %0d", AC);
            $display("Real BC     = %0d", BC);
            
            $display("A              = %b",  A);
            $display("B              = %b",  B);
            $display("C              = %b",  $unsigned(C)); 
            $display("sign extend A  = %b",  se_A);
            $display("sign extend B  = %b",  se_B);
            $display("sign extend C  = %b",  se_C);
            $display("sign extend AC = %b", se_result_AC);
            $display("sign extend BC = %b", se_result_BC);
            $display("Expected AC    = %b",  expected_ac);
            $display("Expected BC    = %b",  expected_bc);
            $display("Real AC        = %b",  AC);
            $display("Real BC        = %b",  BC);
                      
            #10 RST = 1'b1;
            #20 RST = 1'b0;
            repeat(2) $display();
        end
        $display("Pass: %0d", pass_count);
        $display("Fail: %0d", fail_count);    
        #2000 $finish;
    end
    
    always #10 CLK = ~CLK;
endmodule
