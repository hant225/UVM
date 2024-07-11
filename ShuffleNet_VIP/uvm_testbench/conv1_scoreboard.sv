`timescale 1ns / 1ps
`include "uvm_macros.svh"
import uvm_pkg::*;
import conv1_pkg::*;            

//////////////////////////////////////////////////////////////////////////////////

import "DPI-C" function void golden_model();

//////////////////////////////////////////////////////////////////////////////////

class conv1_scoreboard #(
    localparam pDATA_WIDTH    = conv1_pkg::pDATA_WIDTH,
    localparam pINPUT_WIDTH   = conv1_pkg::pINPUT_WIDTH,
    localparam pINPUT_HEIGHT  = conv1_pkg::pINPUT_HEIGHT,
    localparam pIN_CHANNEL    = conv1_pkg::pIN_CHANNEL,
    localparam pOUT_CHANNEL   = conv1_pkg::pOUT_CHANNEL,
    localparam pKERNEL_SIZE   = conv1_pkg::pKERNEL_SIZE,
    localparam pPADDING       = conv1_pkg::pPADDING,
    localparam pSTRIDE        = conv1_pkg::pSTRIDE,
    localparam pOUTPUT_WIDTH  = conv1_pkg::pOUTPUT_WIDTH,
    localparam pOUTPUT_HEIGHT = conv1_pkg::pOUTPUT_HEIGHT,        
    localparam img_data_path  = conv1_pkg::img_data_path,
    localparam result_path    = conv1_pkg::result_path
                        ) extends uvm_scoreboard;
    // Register to Factory
    `uvm_component_utils(conv1_scoreboard) 
    
    // Analysis Imp
    uvm_analysis_imp #(conv1_transaction, conv1_scoreboard) recv;
    
    // Properties
    int addr = 0; 
    int fd = 0;         
    logic [pDATA_WIDTH*pIN_CHANNEL-1:0] arr_data_in [pINPUT_WIDTH*pINPUT_HEIGHT]; 
    logic [pDATA_WIDTH-1:0]             out_fm      [0:pOUT_CHANNEL-1][0:pOUTPUT_WIDTH*pOUTPUT_HEIGHT-1];
            
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
        for (int i = 0; i < pOUT_CHANNEL; i = i + 1) begin
            $writememh($sformatf("%s/DUT_out_channel_%0d.txt", result_path, i), out_fm[i]);
        end                        
    endfunction
    
    // Check Phase
    virtual function void check_phase(uvm_phase phase);
        super.check_phase(phase);
        `uvm_info("SCB", "[CHECK PHASE] START CHECKING PROCESS\n", UVM_NONE)
        predictor();
    endfunction
    
    // Report Phase
    virtual function void report_phase(uvm_phase phase);
        super.report_phase(phase);
        `uvm_info("SCB", "[REPORT PHASE] START CHECKING PROCESS\n", UVM_NONE)
    endfunction
    
    // Write Method
    virtual function void write(conv1_transaction tr);
        if(tr.op == RESET)             
            reset_state();
        else if (tr.op != LOAD_PIXELS && tr.op != PE_RUNNING)  
            `uvm_info("SCB", "LOADING WEIGHTS TO DUT..", UVM_NONE)
        else
            collect_data(tr);
    endfunction           
    
    // Reset State
    function reset_state();
        `uvm_info("SCB", "SYSTEM RESET..", UVM_NONE)
        fd = $fopen(img_data_path, "w");
        if(!fd) `uvm_fatal("SCB", "Unable to create image data file!")
        $fclose(fd);
    endfunction         
    
    // Collect Results
    virtual function collect_data(conv1_transaction tr);    
        // Double check the input image
        if(tr.en) begin
            fd = $fopen(img_data_path, "a");
            if(!fd) `uvm_fatal("SCB", "Unable to open output image data file!")
            $fwrite(fd, "%2h%2h%2h\n", tr.data_in[23:16], tr.data_in[15:8], tr.data_in[7:0]);
            $fclose(fd);
        end
    
        // Collect data_out if tr.valid = 1'b1
        if(tr.valid) begin            
            for (int i = 0; i < pOUT_CHANNEL; i = i + 1) begin
                out_fm[i][addr] = tr.data_out[pDATA_WIDTH*i +: pDATA_WIDTH];
            end
            addr = addr + 1;
        end
    endfunction
    
    // Predictor
    function predictor();   
        `uvm_info("SCB", "Start checking result..", UVM_NONE);
        golden_model();                   
    endfunction
      
endclass : conv1_scoreboard



