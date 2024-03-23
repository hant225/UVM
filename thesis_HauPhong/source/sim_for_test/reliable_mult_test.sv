`timescale 1ns / 1ps
//////////////////////////////////////////////////////////////////////////////////
// Company: 
// Engineer: 
// 
// Create Date: 03/22/2024 01:09:23 PM
// Design Name: 
// Module Name: reliable_mult_test
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


module reliable_mult_test;
    logic signed [7:0]  A;
    logic        [7:0]  uB;
    logic signed [7:0]  sB;
    logic signed [31:0] P;
    
    logic signed [7:0] dutA;
    logic        [7:0] dutB;
    logic signed [15:0] result;
    
    logic signed [15:0] se_A;
    logic signed [15:0] se_B;
    logic        [31:0] se_result;
    initial begin
        dutA = -35;
        dutB = 132;
        se_A = dutA;
        se_B = dutB;
        se_result = se_A * se_B;
        result = se_result[15:0];
        
        $display("[BIN]dutA : %b", dutA);
        $display("[BIN]dutB : %b", $unsigned(dutB));
        $display("[DEC]dutA : %0d", dutA);
        $display("[DEC]dutB : %0d", $unsigned(dutB));
        
        $display("[SIGN EXTEND]");
        $display("[BIN]se_A : %b", se_A);
        $display("[BIN]se_B : %b", se_B);
        
        $display("[RESULT]");
        $display("result : %b", result);
        $display("result : %0d", result);
    end
    
//    initial begin
//        A = -56;
//        uB = 130;
//        sB = 130;
//        P = A * uB;
//        $display("[BIN] A  : %b", A);
//        $display("[BIN] uB : %b", uB);
//        $display("[BIN] sB : %b", sB);
//        $display("[DEC] A  : %0d", A);
//        $display("[DEC] uB : %0d", uB);
//        $display("[DEC] sB : %0d", sB);
        
//        $display("[unsigned] %0d * %0d = %0d", A, $unsigned(uB[7:0]), P);
//        $display("[unsigned] result = %b", P);
//        P = A * sB;
//        $display("[signed]   %0d * %0d = %0d", A, sB, P);
//        $display("[signed] result = %b", P);
//        //////////////////////////////////////////////////////////////
//        A = 56;
//        uB = 112;
//        sB = 112;
//        P = A * uB;
//        $display("A : %b", A);
//        $display("B : %b", $unsigned(uB));
//        $display("[unsigned] %0d * %0d = %0d", A, uB, P);
//        $display("[unsigned] result = %b", P);
//        P = A * sB;
//        $display("[signed]   %0d * %0d = %0d", A, sB, P);
//        $display("[signed] result = %b", P);
//        $display();
//        //////////////////////////////////////////////////////////////
//        repeat(10) begin
//            A = $random();
//            uB = $urandom();
//            sB = uB;
//            P = A * uB;
//            $display("A : %b", A);
//            $display("B : %b", $unsigned(uB));
//            $display("[unsigned] %0d * %0d = %0d", A, uB, P);
//            $display("[unsigned] result = %b", P);
//            P = A * sB;
//            $display("[signed]   %0d * %0d = %0d", A, sB, P);
//            $display("[signed] result = %b", P);
//            $display();
//        end
//    end
endmodule
