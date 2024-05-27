`timescale 1ns / 1ps

module SVA_lec13(
    input a, b, sel,
    output reg y, err
);

    always_comb begin
        if(sel == 1'b1)
            assert (y == a) begin
                err = 1'b0;
            end else begin
                $error("y is not equal to a");
                err = 1'b1;
            end 
        else
            assert (y == b) begin
                err = 1'b0;
            end else begin
                $error("y is not equal to b");
                err = 1'b1;
            end
    end
endmodule
