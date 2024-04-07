
module test1;

  typedef bit [2:0] A;

  typedef struct packed { bit a; bit b; bit c; } S;

  typedef union packed { A a; S s; } U;

  bit b [3:12];  
  S s;
  U u;
  A a;
  logic l0, l1, lz, lx;
  logic [11:23] lpa;
  

  import "DPI-C" function void f(input A a, 
                                 input S s, 
                                 input U u, 
                                 input bit b[3:12], 
                                 input logic l0, 
                                 input logic l1, 
                                 input logic lz, 
                                 input logic lx, 
                                 input logic [11:23] la);
  
  initial begin
    s.a = 1'b1;
    s.b = 1'b0;
    s.c = 1'b0;
    a = 3'b100;
    u.a = 3'b100;
    l0 = 1'b0;
    l1 = 1'b1;
    lz = 1'bz;
    lx = 1'bx;
    lpa = 13'bx_zzzz_1111_0000;
    
    for(int i = 3; i <= 12; i++)
      b[i] = (i % 3) & 1'b1;

    f(a, s, u, b, l0, l1, lz, lx, lpa);
  end
  
endmodule

