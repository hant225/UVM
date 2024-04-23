`timescale 1ns / 1ps
`include "uvm_macros.svh"
import uvm_pkg::*;

//////////////////////////////////////////////////////////////////////////////////

typedef logic [63:0] ultra_ram_queue [$:4];

// DPI Import                                          
import "DPI-C" function void c_mac ( input  int                  pixel_data, 
                                     input  int                  weight_data, 
                                     input  int                  reg_data,
                                     output logic signed [31:0]  mac_out);
                                            
import "DPI-C" function void c_bias ( input  int                 bias_in,
                                      input  int                 bias_weight,
                                      output logic signed [31:0] bias_out );
                                     
import "DPI-C" function void c_sigmoid ( input  int                 actv_in,
                                         output logic signed [31:0] actv_out);
                                        
import "DPI-C" function void c_quantize ( input  int                 quant_in,
                                          output logic signed [31:0] quant_out);

//////////////////////////////////////////////////////////////////////////////////

class scoreboard extends uvm_monitor;
    // Local Parameters
    localparam pKERNEL_SIZE  = 9;
    localparam pBIAS_NUM     = 16;
    localparam pBASE_ADDRESS = 'h40000000; 

    // Extern Functions
    extern virtual function void mirror_mem(transaction tr);
    extern virtual function void predictor();
    extern virtual function void sv_arr_get_data_ready();
    extern virtual function void sv_dequantize(input  logic signed [31:0] multiplicand, 
                                               input  logic signed [31:0] multiplier, 
                                               output logic signed [31:0] deq_result);
    extern virtual function void sv_golden_model();
    
    // Properties - Mem Mirror
    ultra_ram_queue virtual_mem [int];

    // Properties - File Handle
    int fd;
    string virtual_mem_path = "/home/hao/Documents/0.KHOA_LUAN_TOT_NGHIEP/log_dir/virtual_mem.txt";
    
    // Properties For Result Evaluation
    transaction real_result_q [$];  
    logic        [71:0]  data_in;   
    logic        [255:0] expected_data_out;
    logic        [7:0]   arr_gm_data_in [pKERNEL_SIZE];
    logic signed [31:0]  arr_gm_filter_reg [32];
    logic signed [255:0] arr_gm_weight_data [pKERNEL_SIZE];
    logic signed [63:0]  arr_gm_bias_weight [pBIAS_NUM];
    logic signed [31:0]  gm_scale;
    
    // Register to Factory
    `uvm_component_utils(scoreboard)
    
    // Analysis Imp
    uvm_analysis_imp #(transaction, scoreboard) recv;
    
    // Constructor
    function new(input string path = "SCB", uvm_component parent = null);
        super.new(path, parent);
    endfunction
    
    // Build Phase
    virtual function void build_phase(uvm_phase phase);
        super.build_phase(phase);
        recv = new("recv", this);
    endfunction
    
    // Extract Phase
    virtual function void extract_phase(uvm_phase phase);
        super.extract_phase(phase);
        `uvm_info("SCB", $sformatf("\nSIMULATION FINISHED! Number of collected results : %0d\n", this.real_result_q.size()), UVM_NONE)
        foreach(this.real_result_q[i]) begin
            `uvm_info("SCB_DEBUG", $sformatf("Result Queue size = %0d", real_result_q.size()), UVM_NONE)
            `uvm_info("SCB", $sformatf("Result No.%0d", i), UVM_NONE)
            `uvm_info("SCB", this.real_result_q[i].sprint(), UVM_NONE)
        end
    endfunction
    
    // Check Phase
    virtual function void check_phase(uvm_phase phase);
        super.check_phase(phase);
        `uvm_info("SCB", "[CHECK PHASE] START CHECKING PROCESS\n", UVM_NONE)
        predictor();
    endfunction
    
    // Write Method
    virtual function void write(transaction tr);
        if(tr.op == RESET)
            reset_state();
        else if (tr.op == MEM_KERNEL_LOAD || tr.op == MEM_BIAS_LOAD || tr.op == MEM_SCALE_LOAD)  
            mirror_mem(tr); 
        else
            collect_dut_result(tr);
    endfunction   
    
    // Reset Method
    function void reset_state();
        string file_header = "\
            \n+==============================================================================================================================================================================+\
            \n                                                         SCOREBOARD'S VIRTUAL MEMORY                                                                                                  \
            \n+==============================================================================================================================================================================+\n\
            ";       
             
        `uvm_info("SCB", "SYSTEM RESET", UVM_NONE)
        fd = $fopen(virtual_mem_path, "w");
        if(fd) begin
            `uvm_info("SCB", $sformatf("VIRTUAL MEMORY FILE READY TO WRITE: %s", virtual_mem_path),UVM_NONE)
            $fdisplay(fd, "%s", file_header);
        end else    
            `uvm_error("SCB", "UNABLE TO CREATE VIRTUAL MEMORY FILE!")
        $fclose(fd);
    endfunction
    
    // Collect DUT's Results Method
    function void collect_dut_result(transaction tr);
        transaction deep_cp_obj = new;
        deep_cp_obj.data_in  = tr.data_in;
        deep_cp_obj.data_out = tr.data_out;
        tr.tr_display("SCB");
        real_result_q.push_back(deep_cp_obj);
    endfunction
endclass : scoreboard


//------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------


function void scoreboard::mirror_mem(transaction tr);
    // Local vars
    int i_weight_addr;
    logic [63:0] modified_weight_data;

    `uvm_info("SCB", $sformatf("[MEMORY LOADING] Weight Loaded: weight_addr = %0h , weight_data = %8h_%8h", tr.weight_addr, tr.weight_data[63:32], tr.weight_data[31:0]), UVM_NONE)
    // manipulate weight data to write
    i_weight_addr = tr.weight_addr;                                 // convert logic to int
    modified_weight_data[63:32] = tr.weight_data[31:0];
    modified_weight_data[31:0]  = tr.weight_data[63:32];
    virtual_mem[i_weight_addr].push_back(modified_weight_data);     // push to queue
    
    // write to file if load scale (last to load)
    if(tr.op == MEM_SCALE_LOAD) begin            
        fd = $fopen(virtual_mem_path, "a+");
        if(!fd) `uvm_error("SCB", "UNABLE TO OPEN FILE TO WRITE")
        else begin
            foreach(virtual_mem[i]) begin
                $fwrite(fd, "address: %0h ,", i);
                foreach(virtual_mem[i][j])
                    $fwrite(fd, "  { pos : %0d  data = %8h_%8h }  ", j, virtual_mem[i][j][63:32], virtual_mem[i][j][31:0]);
                $fwrite(fd, "\n");    
            end
        end    
        $fclose(fd);
        `uvm_info("SCB", $sformatf("VIRTUAL MEMORY FILE CREATED: %s\n\n", virtual_mem_path), UVM_NONE)
    end
endfunction : mirror_mem
    
    
//------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------


function scoreboard::predictor();
    foreach(real_result_q[i]) begin
        data_in = real_result_q[i].data_in;
        sv_arr_get_data_ready();
        sv_golden_model();
    end
endfunction : predictor


//------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------


function scoreboard::sv_golden_model();
    int left, right;
    int pixel_data;
    int weight_data;
    int mac_reg;
    int bias_in;
    int actv_in;
    int quant_in;
    logic signed [31:0] mac_out;
    logic signed [31:0] deq_out;
    logic signed [31:0] bias_out;
    logic signed [31:0] actv_out;
    logic signed [31:0] quant_out;
    
    // 1. MAC ...................................................................................................
    for(int i = 0; i < pKERNEL_SIZE; i++) begin
        for(int j = 0; j < 32; j++) begin
            right = j * 8;
            left = right + 8 - 1;
            pixel_data  = arr_gm_data_in[i];
            weight_data = $signed(arr_gm_weight_data[i][left-:8]);      // dont forget to add the $signed() when extract the packed array 
            mac_reg     = $signed(arr_gm_filter_reg[j]);
            
            // Call C function
            c_mac(pixel_data, weight_data, mac_reg, mac_out);
            arr_gm_filter_reg[j] = mac_out;
        end
    end        
    
    // 2. DEQUANTIZE ..........................................................................................
    foreach(arr_gm_filter_reg[i]) begin
        sv_dequantize(arr_gm_filter_reg[i], gm_scale, deq_out);
        arr_gm_filter_reg[i] = deq_out;     // update reg
    end        
    
    // 3. BIAS ................................................................................................        
    for(int i = 0; i < 32; i++) begin
        bias_in     = arr_gm_filter_reg[i];
        weight_data = (i % 2)? $signed(arr_gm_bias_weight[i/2][31:0]) : 
                               $signed(arr_gm_bias_weight[i/2][63:32]); 
        c_bias(bias_in, weight_data, bias_out);
        arr_gm_filter_reg[i] = bias_out;    // update reg
    end        
    
    // 4. ACTIVATION (Sigmoid) ................................................................................        
    foreach(arr_gm_filter_reg[i]) begin
        actv_in = arr_gm_filter_reg[i];
        c_sigmoid(actv_in, actv_out);
        arr_gm_filter_reg[i] = actv_out;    // update reg
    end        
    
    // 5. QUANTIZATION
    foreach(arr_gm_filter_reg[i]) begin
        quant_in = arr_gm_filter_reg[i];
        c_quantize(quant_in, quant_out);
        arr_gm_filter_reg[i] = quant_out;
    end
    
    // 6. FORM OUTPUT
    foreach(arr_gm_filter_reg[i]) begin
        expected_data_out[i*8+7-:8] = arr_gm_filter_reg[i][7:0];
        $display("%h", expected_data_out); 
    end
endfunction : sv_golden_model


//------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------


function scoreboard::sv_arr_get_data_ready();
    int pixel_pos;
    logic signed [63:0] arr_TMP_weight_data [4];      
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
endfunction : sv_arr_get_data_ready


//------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------


function scoreboard::sv_dequantize( input  logic signed [31:0] multiplicand, 
                                    input  logic signed [31:0] multiplier, 
                                    output logic signed [31:0] deq_result );
    
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

    deq_result = $signed(ext_product[47:16]);        // dequantize result
    
endfunction : sv_dequantize
