`timescale 1ns / 1ps
`include "uvm_macros.svh"
import uvm_pkg::*;
import conv1_pkg::*;            

//////////////////////////////////////////////////////////////////////////////////

import "DPI-C" function void gen_conv1_input_and_rslt();

//////////////////////////////////////////////////////////////////////////////////

class conv1_std_seq #(localparam pWEIGHT_BASE_ADDR  = conv1_pkg::pWEIGHT_BASE_ADDR,
                      localparam pIN_CHANNEL        = conv1_pkg::pIN_CHANNEL,
                      localparam pOUT_CHANNEL       = conv1_pkg::pOUT_CHANNEL,
                      localparam pINPUT_WIDTH       = conv1_pkg::pINPUT_WIDTH,
                      localparam pINPUT_HEIGHT      = conv1_pkg::pINPUT_HEIGHT,
                      localparam pULTRA_RAM_NUM     = conv1_pkg::pULTRA_RAM_NUM,
                      localparam pBLOCK_RAM_NUM     = conv1_pkg::pBLOCK_RAM_NUM,
                      localparam pKERNEL_NUM        = conv1_pkg::pKERNEL_NUM,
                      localparam pBIAS_NUM          = conv1_pkg::pBIAS_NUM,
                      localparam pDEQUANT_SCALE_NUM = conv1_pkg::pDEQUANT_SCALE_NUM,
                      localparam pWEIGHTS_NUM       = conv1_pkg::pWEIGHTS_NUM,
                      localparam string weight_path = conv1_pkg::weight_path, 
                      localparam string image_path  = conv1_pkg::image_path,
                      localparam pZEROPOINT_LOAD    = 1                            
                     ) extends uvm_sequence#(conv1_transaction);       
    
    // Register to Factory
    `uvm_object_utils(conv1_std_seq)        
        
    // Properties   
    conv1_transaction tr;    
    int ram_idx = 0;
    int scale   = 0; 
    int addr    = 0;  
    int fd      = 0;        
    int trans_amount = pINPUT_WIDTH * pINPUT_HEIGHT;    
    
    logic [pDATA_WIDTH*pIN_CHANNEL-1:0] in_fm   [0:pINPUT_WIDTH*pINPUT_HEIGHT-1];
    logic [pWEIGHT_DATA_WIDTH-1:0]      weights [0:pWEIGHTS_NUM-1];                
    
    // Constructor
    function new(input string path = "std_seq");
        super.new(path);
    endfunction
    
    // Body
    virtual task body();
        set_response_queue_error_report_disabled(1);
        tr = conv1_transaction::type_id::create("tr");
        do_load_weight(tr);
        `uvm_info("STD_SEQ", "Memory Weights Load Finished. Start Generating Transaction Data!", UVM_NONE)
        create_data_seq(tr);  
        running_state(tr);             
    endtask
    
    // Weight Load Method
    virtual task do_load_weight(conv1_transaction tr);                  
            // Common Signals for loading weights
            tr.rst         = 1'b0;
            tr.en          = 1'b0;
            tr.load_weight = 1'b1;            
                                 
            // Read weights from file here
            fd = $fopen(weight_path, "r");
            if(!fd) `uvm_fatal("SEQ", "Unable to read Weights File");
            $readmemh(weight_path, weights);
            $fclose(fd);                            
                                    
            // 1. Kerrnel weights -----------------------------------------------------------------------------------------------------                     
            for(int i = 0; i < pKERNEL_NUM; i = i + 1) begin
                start_item(tr);                    
                    tr.op          = MEM_KERNEL_LOAD;                      
                    tr.weight_addr = i - ram_idx - (pULTRA_RAM_NUM-1)*scale + pWEIGHT_BASE_ADDR;
                    tr.weight_data = weights[addr++];                    
                finish_item(tr);
                 
                if (ram_idx == pULTRA_RAM_NUM-1) begin
                    ram_idx = 0;
                    scale   = scale + 1;
                end else begin
                    ram_idx = ram_idx + 1;
                end
            end              
                                                           
            // 2. Bias weights --------------------------------------------------------------------------------------------------------
            ram_idx = 0;
            scale   = 0;
            for(int i = 0; i < pBIAS_NUM; i++) begin
                start_item(tr);                    
                    tr.op          = MEM_BIAS_LOAD;
                    tr.weight_addr = i - ram_idx - (pBLOCK_RAM_NUM-1)*scale + pWEIGHT_BASE_ADDR + pKERNEL_NUM/pULTRA_RAM_NUM;
                    tr.weight_data = weights[addr++]; 
                finish_item(tr);                                     

                if (ram_idx == pBLOCK_RAM_NUM-1) begin
                    ram_idx = 0;
                    scale   = scale + 1;
                end else begin
                    ram_idx = ram_idx + 1;
                end
            end
          
            // 3. Dequantize Scale weights --------------------------------------------------------------------------------------------            
            ram_idx = 0;
            scale   = 0;
            load_dequantize_scale_weights(ram_idx, scale);                        
            
            // 4. Quantize Scale weights ----------------------------------------------------------------------------------------------
            repeat(pZEROPOINT_LOAD) begin
                start_item(tr);                
                    tr.op          = MEM_QUANT_SCALE_LOAD;
                    tr.weight_addr = tr.weight_addr + 1;
                    tr.weight_data = weights[addr++];
                finish_item(tr);  
            end
    endtask
    
    // Task for load dequantize weights because CONV1, CONV1x1, CONDW has same load kernel,
    // bias and scale weights method but has a small different in dequant scale weight load.
    // Split the load dequantize scale help overriding this method in child class in the future  
    virtual task load_dequantize_scale_weights(input int ram_idx, input int scale);
        for(int i = 0; i < pDEQUANT_SCALE_NUM; i++) begin
            start_item(tr);                    
                tr.op          = MEM_DEQUANT_SCALE_LOAD;
                tr.weight_addr = i - ram_idx - (pBLOCK_RAM_NUM-1)*scale + pWEIGHT_BASE_ADDR + pKERNEL_NUM/pULTRA_RAM_NUM + 1;
                tr.weight_data = weights[addr++];
            finish_item(tr);                                    
            
            if(ram_idx == pOUT_CHANNEL-1) begin
                ram_idx = 0;
                scale   = scale + 1;
            end else begin
                ram_idx = ram_idx + 1;
            end
        end
    endtask
    
    // Create Data Sequence Method
    virtual task create_data_seq(conv1_transaction tr);                              
        gen_conv1_input_and_rslt();                           // Call C routine
        $readmemh(image_path, in_fm);                         // Read image to array                                           
        for(int i = 0; i < trans_amount; i++) begin           // Create seq items
            start_item(tr);
                tr.op           = LOAD_PIXELS;                            
                tr.rst          = 1'b0;                
                tr.load_weight  = 1'b0;                
                tr.en           = 1'b1;           
                tr.data_in      = in_fm[i];     
                `uvm_info("STD_SEQ", $sformatf("[No.%0d] Transaction Generated: data_in = %0h", i, tr.data_in), UVM_NONE)
            finish_item(tr);
        end
    endtask
    
    // Finish Loading Weight and Pixel, Wait for PE to Finish
    virtual task running_state(conv1_transaction tr);
        start_item(tr);
            tr.op          = PE_RUNNING;
            tr.rst         = 1'b0;
            tr.en          = 1'b0;
            tr.load_weight = 1'b0;
            tr.weight_data =  'dx;
            tr.data_in     =  'dx;
        finish_item(tr);                
    endtask
    
endclass
