`timescale 1ns / 1ps
//////////////////////////////////////////////////////////////////////////////////
module test_plus_2_svLogic;
    logic signed [7:0]  a;
    logic signed [7:0]  b;
    logic signed [7:0]  s;
    logic signed [15:0] p;
    int ia, ib;
    
    import "DPI-C" function void test_thang(input int ia,
                                            input int ib,
                                            output logic signed [7:0] s,
                                            output logic signed [15:0] p
                                            );
    initial begin
        a = -8'd19;
        b = 8'd50;
        ia = a;
        ib = b;
        test_thang(ia, ib, s, p);
        $display("[SV] s : %0d", s);
        $display("[SV] p : %0d", p);
    end    
endmodule
