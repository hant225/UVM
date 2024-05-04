`timescale 1ns / 1ps

//////////////////////////////////////////////////////////////////////////////////

class FP_weight_limit;
    // Properties
    rand logic signed [63:0] weight_data;

    // Constraint
    constraint weight_data_c {weight_data[63:48] inside {[0:1]} ||
                              weight_data[63:48] inside {[65534:65535]};       
                              weight_data[31:16] inside {[0:1]} ||
                              weight_data[31:16] inside {[65534:65535]}; }                      
                               
    // Methods
    function void display();
        $display("upper: %b %f", weight_data[63:32], $itor($signed(weight_data[63:32]))*(2.0**(-16.0)));
        $display("lower: %b %f", weight_data[31:0], $itor($signed(weight_data[31:0]))*(2.0**(-16.0)));
        
        $display();
    endfunction
endclass


module test_constraint;
    FP_weight_limit A;
    
    initial begin
        repeat(1000) begin
            A = new();
            A.randomize();
            A.display();
        end
    end
endmodule
