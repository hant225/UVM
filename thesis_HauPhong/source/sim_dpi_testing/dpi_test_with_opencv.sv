`timescale 1ns / 1ps

//////////////////////////////////////////////////////////////////////////////////

module dpi_test_with_opencv;
    import "DPI-C" function int main();
    int tmp;
    initial begin
        tmp = main();
        #2000 $finish;
    end
endmodule
