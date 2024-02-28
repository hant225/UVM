`timescale 1ns / 1ps
//////////////////////////////////////////////////////////////////////////////////
// Company: 
// Engineer: 
// 
// Create Date: 02/07/2024 07:46:32 PM
// Design Name: 
// Module Name: testp_override
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

//////////////////////////////////////////////////////////////////////////////////

class A;
    function call();
        $display("This is call() method of A class!");
    endfunction
endclass

//////////////////////////////////////////////////////////////////////////////////

class A_1 extends A;
//    function call();
//        $display("This is call() method of A_1 class!");
//    endfunction
endclass

//////////////////////////////////////////////////////////////////////////////////

module testp_override;
    A a;
    A_1 a1;
    
    initial begin
        a = new();
        a1 = new();
        a.call();
        a1.call();
    end
endmodule
