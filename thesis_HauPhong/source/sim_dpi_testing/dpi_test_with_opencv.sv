`timescale 1ns / 1ps

//////////////////////////////////////////////////////////////////////////////////

module dpi_test_with_opencv;

    import "DPI-C" function void dumamay();
   
    initial begin
        dumamay();
        #2000 $finish;
    end
endmodule
