`timescale 1ns / 1ps
`include "uvm_macros.svh"
import uvm_pkg::*;
import my_pkg::*;

//////////////////////////////////////////////////////////////////////////////////

class std_seq extends uvm_sequence#(transaction);   
    // Register to Factory
    `uvm_object_utils(std_seq)        

    // Properties   
    transaction tr;    
    int ram_idx = 0;
    int scale   = 0; 
    int addr    = 0;  
    int fd      = 0;
    int trans_amount = pINPUT_WIDTH * pINPUT_HEIGHT;    
    
    logic [pWEIGHT_DATA_WIDTH-1:0] weights [0:pWEIGHTS_NUM-1];        
    string weight_path = "/home/hao/Documents/0.KHOA_LUAN_TOT_NGHIEP/shuffle_net/HauPhong_Weight/total_weights.txt"; 
    
    // Constructor
    function new(input string path = "std_seq");
        super.new(path);
    endfunction
    
    // Body
    virtual task body();
        set_response_queue_error_report_disabled(1);
        tr = transaction::type_id::create("tr");
        do_load_weight(tr);
        `uvm_info("STD_SEQ", "Memory Weights Load Finished. Start Generating Transaction Data!", UVM_NONE)
        create_data_seq(tr);  
        running_state(tr);             
    endtask
    
    // Weight Load Method
    task do_load_weight(transaction tr);                
            // Turn off constraints
            tr.cred.constraint_mode(0);
            tr.cblue.constraint_mode(0);
            tr.cgreen.constraint_mode(0);                        
                  
            // Common Signals for loading weights
            tr.rst         = 1'b0;
            tr.en          = 1'b0;
            tr.load_weight = 1'b1;            
                                 
            // Read weights from file here
            fd = $fopen(weight_path, "r");
            if(!fd) `uvm_fatal("SEQ", "Unable to read Weights File");
            $readmemh(weight_path, weights);
            $fclose(fd);                           
                                    
            // Kerrnel weights -----------------------------------------------------------------------------------------------------                     
            for(int i = 0; i < pKERNEL_NUM; i = i + 1) begin
                start_item(tr);
                    assert(tr.randomize());
                    tr.op          = MEM_KERNEL_LOAD;                      
                    tr.weight_addr    = i - ram_idx - (pULTRA_RAM_NUM-1)*scale + pWEIGHT_BASE_ADDR;
                    tr.weight_data    = weights[addr++];                    
                finish_item(tr);
                
                ram_idx = (ram_idx == pULTRA_RAM_NUM-1)? 0 : ram_idx + 1;
                scale   = (ram_idx == pULTRA_RAM_NUM-1)? scale + 1 : scale; 
            end            
                                                           
            // Bias weights --------------------------------------------------------------------------------------------------------
            ram_idx = 0;
            scale   = 0;
            for(int i = 0; i < pBIAS_NUM; i++) begin
                start_item(tr);
                    assert(tr.randomize());
                    tr.op       = MEM_BIAS_LOAD;
                    tr.weight_addr = i - ram_idx - (pBLOCK_RAM_NUM-1)*scale + pWEIGHT_BASE_ADDR + pKERNEL_NUM/pULTRA_RAM_NUM;
                    tr.weight_data = weights[addr++]; 
                finish_item(tr);     
                
                ram_idx = (ram_idx == pBLOCK_RAM_NUM-1)? 0 : ram_idx + 1;
                scale   = (ram_idx == pBLOCK_RAM_NUM-1)? scale + 1 : scale;
            end
            
            // Dequantize Scale weights --------------------------------------------------------------------------------------------
            ram_idx = 0;
            scale   = 0;
            for(int i = 0; i < pDEQUANT_SCALE_NUM; i++) begin
                start_item(tr);
                    assert(tr.randomize());
                    tr.op       = MEM_DEQUANT_SCALE_LOAD;
                    tr.weight_addr = i - ram_idx - (pBLOCK_RAM_NUM-1)*scale + pWEIGHT_BASE_ADDR + pKERNEL_NUM/pULTRA_RAM_NUM + 1;
                    tr.weight_data = weights[addr++];
                finish_item(tr);    
                
                ram_idx = (ram_idx == pOUT_CHANNEL-1)? 0 : ram_idx + 1;
                scale   = (ram_idx == pOUT_CHANNEL-1)? scale + 1 : scale; 
            end
            
            // Quantize Scale weights ----------------------------------------------------------------------------------------------
            start_item(tr);
                assert(tr.randomize());
                tr.op       = MEM_QUANT_SCALE_LOAD;
                tr.weight_addr = tr.weight_addr + 1;
                tr.weight_data = weights[addr++];
            finish_item(tr);  
    endtask
    
    // Create Data Sequence Method
    task create_data_seq(transaction tr);
        tr.op = LOAD_PIXELS;
        for(int i = 0; i < trans_amount; i++) begin
            start_item(tr);
                /* Turn constraints on/off here */
                assert(tr.randomize());
                tr.rst          = 1'b0;                
                tr.load_weight  = 1'b0;                
                tr.en           = 1'b1;                
                `uvm_info("STD_SEQ", $sformatf("[No.%0d] Transaction Generated: data_in = %0h", i, tr.data_in), UVM_NONE)
            finish_item(tr);
        end
    endtask
    
    // Finish Loading Weight and Pixel, Wait for PE to Finish
    task running_state(transaction tr);
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

