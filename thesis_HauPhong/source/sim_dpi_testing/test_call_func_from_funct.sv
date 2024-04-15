`timescale 1ns / 1ps

//////////////////////////////////////////////////////////////////////////////////

// Class for generate random floating point number
class fp_num_rand;
    rand logic signed [15:0] fp_dec;
    rand logic        [15:0] fp_frac;
    constraint fp_dec_c {fp_dec inside {[-8:8]};}
endclass

// Transaction class clone
class transaction;
    logic signed [71:0] data_in;
    logic [255:0] data_out;
endclass

//////////////////////////////////////////////////////////////////////////////////

module test_call_func_from_funct;
  
    // Properties
    fp_num_rand a;
    logic signed [31:0] fp_num;
    logic [31:0] result;
    logic signed [31:0] q_fp_num [$];
    logic signed [31:0] q_result [$];
    
     // Properties - Result Evaluation
    transaction q_dut_rslt [$];
    transaction q_expected_rslt [$]; 
    int filter_num  = 32;
    int kernel_size = 9;
    logic [31:0] arr_adder_tree [32];
    
    // DPI Import
    import "DPI-C" function void test_thang();
    import "DPI-C" function void golden_model( output logic [31:0] result,
                                               input logic [31:0] A); 
    
    function create_dut_rslt(input int trans_amount, input bit display_queue);
        transaction tr;
        fp_num_rand gen_fn;
                
        repeat(trans_amount) begin
            tr     = new();
            gen_fn = new();
            gen_fn.randomize();
            tr.data_in = {gen_fn.fp_dec, gen_fn.fp_frac};
            q_dut_rslt.push_back(tr);
        end
        $display("%0d of transactions are created!", q_dut_rslt.size());
        
        if(display_queue) begin
            foreach(q_dut_rslt[i])
                $display("[%2d]%32b - %0f,", i, q_dut_rslt[i].data_in, $itor(q_dut_rslt[i].data_in)*(2.0**(-16.0)));
        end
    endfunction
    
    initial begin
        create_dut_rslt(100, 1);
//        a = new;
//        repeat(100) begin
//            a.randomize();
//            fp_num = {a.fp_dec, a.fp_frac};
//            $display("--------------------------------------------------------");
//            $display("[FLOAT] fp_num = %0f", $itor(fp_num)*(2.0**(-16.0)));
//            golden_model(result, fp_num);
//            $display("[SV] FLOAT result of C-do_sigmoid : %f", $itor(result)*(2.0**(-16.0)));
//            $display("--------------------------------------------------------\n");
//            // DEBUG ONLY START
//            q_fp_num.push_back(fp_num);
//            q_result.push_back(result);
//            // DEBUG ONLY END
//        end
        // test_thang();
    end
    
endmodule
