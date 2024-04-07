`timescale 1ns / 1ps
//////////////////////////////////////////////////////////////////////////////////
module test_plus_2_svLogic;
    logic [7:0] A;
    logic [7:0] B;
    logic [7:0] C;
    int iA, iB, iC;
    
    import "DPI-C" function int plus8bit(input int iA, input int iB);
    
    initial begin
        repeat (10) begin
            #10;
            A = $urandom();
            B = $urandom();
            iA = A;
            iB = B;
            iC = plus8bit(iA, iB);
            C = iC;
            $display("[SV] %0d + %0d = %0d", A, B, C);
        end
    end
endmodule
