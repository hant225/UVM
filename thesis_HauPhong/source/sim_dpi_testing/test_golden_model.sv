`timescale 1ns / 1ps

//////////////////////////////////////////////////////////////////////////////////

typedef logic [63:0] ultra_ram_queue [$:4];

module test_golden_model;
    localparam pKERNEL_SIZE  = 9;
    localparam pBIAS_NUM     = 16;
    localparam pBASE_ADDRESS = 'h40000000; 
    logic [71:0]  data_in;
    logic [255:0] real_data_out;
    logic [255:0] expected_data_out;
    
    ultra_ram_queue virtual_mem [int];
    logic        [7:0]   arr_gm_data_in [pKERNEL_SIZE];
    logic signed [31:0]  arr_gm_filter_reg [32];
    logic signed [255:0] arr_gm_weight_data [pKERNEL_SIZE];
    logic signed [63:0]  arr_gm_bias_weight [pBIAS_NUM];
    logic signed [31:0]  gm_scale;

    // DPI Import                                          
    import "DPI-C" function void c_mac ( input  logic [7:0]  pixel_data,
                                         input  logic signed [7:0]  weight_data,
                                         input  logic signed [31:0] reg_data,
                                         output logic signed [31:0]  mac_out);
                                                
    import "DPI-C" function void c_bias ( input  logic signed [31:0] bias_in,
                                          input  logic signed [31:0] bias_weight,
                                          output logic signed [31:0] bias_out );
                                         
    import "DPI-C" function void c_sigmoid ( input  logic signed [31:0] actv_in,
                                             output logic signed [31:0] actv_out);
                                            
    import "DPI-C" function void c_quantize ( input  logic signed [31:0] quant_in,
                                              output logic signed [31:0] quant_out);
                                                                              
    initial begin
        init_data_and_mem();
        sv_arr_get_data_ready();
        sv_golden_model();
        $finish;
    end
       
    //---------------------------------------------------------------------------------------------------------------------------
    
    function sv_arr_get_data_ready();
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
        
        // initialize value for adder tree
        foreach(arr_gm_filter_reg[i]) begin
            arr_gm_filter_reg[i] = 32'd0;
        end
        
        // get scale data - scale of virtual_mem[scale][63:32] (dequant_scale_r[31:0])
        gm_scale = virtual_mem[pBASE_ADDRESS + pKERNEL_SIZE + pBIAS_NUM][0][63:32];
        
        // get bias data
        for(int i = 0; i < pBIAS_NUM; i++) begin
            arr_gm_bias_weight[i] = virtual_mem[pBASE_ADDRESS + pKERNEL_SIZE + i][0];
        end
    endfunction
    
    //---------------------------------------------------------------------------------------------------------------------------
    
    function sv_golden_model();
        int left, right;
        logic [7:0]  pixel_data;
        logic signed [7:0]  weight_data;
        logic signed [31:0] mac_out;
        logic signed [31:0] deq_out;
        logic signed [31:0] actv_out;
        logic signed [31:0] quant_out;
        
        // MAC 
        for(int i = 0; i < pKERNEL_SIZE; i++) begin
            for(int j = 0; j < 32; j++) begin
                right = j * 8;
                left = right + 8 - 1;
                pixel_data  = arr_gm_data_in[i];
                weight_data = arr_gm_weight_data[i][left-:8];
                // Call C function
                c_mac(pixel_data, weight_data, arr_gm_filter_reg[j], mac_out);
                arr_gm_filter_reg[j] = mac_out;
            end
        end
        
        debug_filter_reg("MAC");                                    // DEBUG
        
        // DEQUANTIZE
        foreach(arr_gm_filter_reg[i]) begin
            sv_dequantize(arr_gm_filter_reg[i], gm_scale, deq_out);
            arr_gm_filter_reg[i] = deq_out;     // update reg
        end
        
        debug_filter_reg("DEQUANTIZE");                             // DEBUG
        
        // BIAS
        for(int i = 0; i < 32; i++) begin
            logic [31:0] bias_out;
            if(i % 2) 
                c_bias(arr_gm_filter_reg[i], arr_gm_bias_weight[i/2][31:0], bias_out);
            else 
                c_bias(arr_gm_filter_reg[i], arr_gm_bias_weight[i/2][63:32], bias_out);
            arr_gm_filter_reg[i] = bias_out;    // update reg
        end
        
        debug_filter_reg("BIAS");                                   // DEBUG
        
        // ACTIVATION (Sigmoid)
        foreach(arr_gm_filter_reg[i]) begin
            c_sigmoid(arr_gm_filter_reg[i], actv_out);
            arr_gm_filter_reg[i] = actv_out;    // update reg
        end
        
        debug_filter_reg("ACTIVATION");                             // DEBUG
        
        // QUANTIZATION
        foreach(arr_gm_filter_reg[i]) begin
            c_quantize(arr_gm_filter_reg[i], quant_out);
            arr_gm_filter_reg[i] = quant_out;
            $display("reg[%2d] after quantize : %b", i, arr_gm_filter_reg[i]);                     // DEBUG        
        end
        
        // FORM OUTPUT
        foreach(arr_gm_filter_reg[i]) begin
            expected_data_out[i*8+7-:8] = arr_gm_filter_reg[i][7:0];
            $display("%h", expected_data_out); 
        end
        
    endfunction
    
    //---------------------------------------------------------------------------------------------------------------------------
    
    function debug_filter_reg(input string ID);
        foreach(arr_gm_filter_reg[i]) begin
//            $display("[SV-%s] reg_%2d : %b", ID, i, arr_gm_filter_reg[i]);
//            $display("[SV-%s] reg_%2d : %h", ID, i, arr_gm_filter_reg[i]);
            $display("[SV-%s] reg_%2d : %f", ID, i, $itor(arr_gm_filter_reg[i])*((2.0)**(-16.0)));
        end
    endfunction
    
    //---------------------------------------------------------------------------------------------------------------------------
    
    function sv_dequantize(input  logic signed [31:0] multiplicand, 
                           input  logic signed [31:0] multiplier, 
                           output logic signed [31:0] deq_result);
                           
        bit signed [63:0]  ext_multiplicand;
        bit signed [63:0]  ext_multiplier;
        bit signed [127:0] ext_product;
        bit signed [127:0] arr_partial[64];
        
        ext_product      = 0;                    // remember to init if var is defined as signed
        ext_multiplicand = multiplicand;
        ext_multiplier   = multiplier;
        
        for(int i = 0; i < 64; i++)  begin
            if(ext_multiplier[i]) 
                arr_partial[i] = ext_multiplicand;
            arr_partial[i] = arr_partial[i] <<< i;
        end

        foreach(arr_partial[i]) begin
            ext_product += arr_partial[i];
        end

        deq_result = ext_product[47:16];        // dequantize result
    endfunction
    
    //---------------------------------------------------------------------------------------------------------------------------
    
    function init_data_and_mem();           // might delete later
        int pos = 0;
        logic [63:0] arr_weight_linear [53];
        data_in = 72'b00110011_10000100_11010110_11111101_11111100_11111101_10001110_01100110_01010010;
        
        $readmemh("/home/hao/Documents/0.KHOA_LUAN_TOT_NGHIEP/log_dir/mem_for_test_source.txt", arr_weight_linear);
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
    endfunction
endmodule