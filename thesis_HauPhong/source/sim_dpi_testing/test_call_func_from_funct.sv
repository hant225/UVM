`timescale 1ns / 1ps
//////////////////////////////////////////////////////////////////////////////////
// Company: 
// Engineer: 
// 
// Create Date: 04/07/2024 12:00:29 PM
// Design Name: 
// Module Name: test_call_func_from_funct
// Project Name: 
// Target Devices: 
// Tool Versions: 
// Description: 
// 
// Dependencies: 
// 
// Revision:
// Revision 0.01 - File Created
// Additional Comments:
// 
//////////////////////////////////////////////////////////////////////////////////

module test_call_func_from_funct;
    // Class for generate random floating point number
    class fp_num_rand;
        rand logic signed [15:0] fp_dec;
        rand logic        [15:0] fp_frac;
        constraint fp_dec_c {fp_dec inside {[-8:8]};}
    endclass
    
    // Properties
    fp_num_rand a;
    logic signed [31:0] fp_num;
    logic [31:0] result;
      
    
    // DPI Import
    import "DPI-C" function void test_thang();
    import "DPI-C" function void golden_model( output logic [31:0] result,
                                               input logic [31:0] A); 
    
    initial begin
        a = new;
        repeat(1) begin
            a.randomize();
            fp_num = {a.fp_dec, a.fp_frac};
            $display("[FLOAT] fp_num = %0f", $itor(fp_num)*(2.0**(-16.0)));
            $display("[BIN]   fp_num = %0b", fp_num);
        end
        golden_model(result, fp_num);
//        test_thang();
    end
endmodule
