`timescale 1ns / 1ps

//////////////////////////////////////////////////////////////////////////////////

typedef logic [63:0] ultra_ram_queue [$:4];

module test_golden_model;
    localparam pKERNEL_SIZE  = 9;
    localparam pBASE_ADDRESS = 'h40000000; 
    logic [71:0]  data_in;
    logic [255:0] real_data_out;
    logic [255:0] expected_data_out;
    
    ultra_ram_queue virtual_mem [int];
    logic [7:0]   arr_gm_data_in [pKERNEL_SIZE];
    logic [255:0] arr_gm_weight_data [pKERNEL_SIZE];
    // DPI Import
    import "DPI-C" function void test_thang();
    import "DPI-C" function void golden_model( output logic [31:0] result,
                                               input logic [31:0] pixel); 
    
    initial begin
        init_data_and_mem();
        sv_arr_data_and_weight_ready();
        sv_golden_model();
        $finish;
    end
    
    function sv_arr_data_and_weight_ready();
        int pixel_pos;
        logic [63:0] arr_TMP_weight_data [4];      
        // seperate pixel of image
        arr_gm_data_in[0] = data_in[71:64];
        arr_gm_data_in[1] = data_in[63:56];
        arr_gm_data_in[2] = data_in[55:48];
        arr_gm_data_in[3] = data_in[47:40];
        arr_gm_data_in[4] = data_in[39:32];
        arr_gm_data_in[5] = data_in[31:24];
        arr_gm_data_in[6] = data_in[23:16];
        arr_gm_data_in[7] = data_in[15:8];
        arr_gm_data_in[8] = data_in[7:0];   
        
        // get kernel weight of pixel (32 filters) and store into 4 chunks of 64 bits
        for(pixel_pos = 0; pixel_pos < pKERNEL_SIZE; pixel_pos++) begin
            foreach(virtual_mem[pBASE_ADDRESS + pixel_pos][i]) begin
                arr_TMP_weight_data[i][63:32] = virtual_mem[pBASE_ADDRESS + pixel_pos][i][31:0];     // Flip lower and higher
                arr_TMP_weight_data[i][31:0]  = virtual_mem[pBASE_ADDRESS + pixel_pos][i][63:32];    // Flip lower and higher
            end
            // Create weight data in correct order
            arr_gm_weight_data[pixel_pos][255:192] = arr_TMP_weight_data[3];
            arr_gm_weight_data[pixel_pos][191:128] = arr_TMP_weight_data[2];
            arr_gm_weight_data[pixel_pos][127:64]  = arr_TMP_weight_data[1];
            arr_gm_weight_data[pixel_pos][63:0]    = arr_TMP_weight_data[0]; 
        end 
    endfunction
    
    function init_data_and_mem();           // might delete later
        int pos = 0;
        logic [63:0] arr_weight_linear [53];
        data_in = 72'b10100111_10110100_01010110_01001010_01010111_11110100_01101000_11011000_10101000;
        
        $readmemh("/home/hao/Documents/0.KHOA_LUAN_TOT_NGHIEP/log_dir/mem_for_test.txt", arr_weight_linear);
        for(int i = 0; i < 9; i++) begin
            for(int j = 0; j < 4; j++) begin
                virtual_mem[pBASE_ADDRESS + i].push_back(arr_weight_linear[pos]);
                pos++;
            end
        end
        for(int i = 0; i < 17; i++) begin
            virtual_mem[pBASE_ADDRESS + 9 + i].push_back(arr_weight_linear[pos]);
                pos++;
        end
        foreach(virtual_mem[i]) begin
            $write("address: %0h ,", i);
            foreach(virtual_mem[i][j]) begin
                $write("  { pos : %0d  data = %8h_%8h }  ", j, virtual_mem[i][j][63:32], virtual_mem[i][j][31:0]);
            end
            $write("\n");    
        end
    endfunction
endmodule