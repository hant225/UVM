`timescale 1ns / 1ps
`include "uvm_macros.svh"
import uvm_pkg::*;
import convDW_pkg::*;

//////////////////////////////////////////////////////////////////////////////////

class conDW_std_seq extends conv1_std_seq#(
                    .pWEIGHT_BASE_ADDR (convDW_pkg::pWEIGHT_BASE_ADDR),
                    .pIN_CHANNEL       (convDW_pkg::pIN_CHANNEL),
                    .pOUT_CHANNEL      (convDW_pkg::pOUT_CHANNEL),
                    .pINPUT_WIDTH      (convDW_pkg::pINPUT_WIDTH),
                    .pINPUT_HEIGHT     (convDW_pkg::pINPUT_HEIGHT),
                    .pULTRA_RAM_NUM    (convDW_pkg::pULTRA_RAM_NUM),
                    .pBLOCK_RAM_NUM    (convDW_pkg::pBLOCK_RAM_NUM),
                    .pKERNEL_NUM       (convDW_pkg::pKERNEL_NUM),
                    .pBIAS_NUM         (convDW_pkg::pBIAS_NUM),
                    .pDEQUANT_SCALE_NUM(convDW_pkg::pDEQUANT_SCALE_NUM),
                    .pWEIGHTS_NUM      (convDW_pkg::pWEIGHTS_NUM),
                    .weight_path       (convDW_pkg::weight_path), 
                    .image_path        (convDW_pkg::image_path),
                    .pZEROPOINT_LOAD   (2) );

    // Register to Factory
    `uvm_object_utils(conDW_std_seq)    
    
    // Properties   
    convDW_transaction tr;                   
    
    // Constructor
    function new(input string path = "std_seq");
        super.new(path);
    endfunction
    
    // Body
    virtual task body();
        set_response_queue_error_report_disabled(1);
        tr = convDW_transaction::type_id::create("tr");
        do_load_weight(tr);
        `uvm_info("STD_SEQ", "Memory Weights Load Finished. Start Generating Transaction Data!", UVM_NONE)
        create_data_seq(tr);  
        running_state(tr);             
    endtask
     
    // Weight Load Method
    task do_load_weight(convDW_transaction tr); 
        super.do_load_weight(tr);
    endtask 
    
    // Load Dequantize Scale Weights Methods
    virtual task load_dequantize_scale_weights(input int ram_idx, input int scale);
        super.load_dequantize_scale_weights(ram_idx, scale);
    endtask
    
    // Create Data Sequence Method
    task create_data_seq(convDW_transaction tr);
        super.create_data_seq(tr);
    endtask
    
    // Finish Loading Weight and Pixel, Wait for PE to Finish
    task running_state(convDW_transaction tr);
        super.running_state(tr);
    endtask
    
endclass