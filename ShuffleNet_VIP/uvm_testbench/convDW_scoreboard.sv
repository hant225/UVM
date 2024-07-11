`timescale 1ns / 1ps
`include "uvm_macros.svh"
import uvm_pkg::*;
import conv1_pkg::*;            

//////////////////////////////////////////////////////////////////////////////////

class convDW_scoreboard extends conv1_scoreboard #(.pDATA_WIDTH    (convDW_pkg::pDATA_WIDTH),
                                                   .pINPUT_WIDTH   (convDW_pkg::pINPUT_WIDTH),
                                                   .pINPUT_HEIGHT  (convDW_pkg::pINPUT_HEIGHT),
                                                   .pIN_CHANNEL    (convDW_pkg::pIN_CHANNEL),
                                                   .pOUT_CHANNEL   (convDW_pkg::pOUT_CHANNEL),
                                                   .pKERNEL_SIZE   (convDW_pkg::pKERNEL_SIZE),
                                                   .pPADDING       (convDW_pkg::pPADDING),
                                                   .pSTRIDE        (convDW_pkg::pSTRIDE),
                                                   .pOUTPUT_WIDTH  (convDW_pkg::pOUTPUT_WIDTH),
                                                   .pOUTPUT_HEIGHT (convDW_pkg::pOUTPUT_HEIGHT),        
                                                   .img_data_path  (convDW_pkg::img_data_path),
                                                   .result_path    (convDW_pkg::result_path) );        
    // Register to Factory
    `uvm_component_utils(convDW_scoreboard) 
    
    // Analysis Imp
    uvm_analysis_imp #(convDW_transaction, convDW_scoreboard) recv;        
            
    // Constructor
    function new(input string path = "SCB", uvm_component parent = null);
        super.new(path, parent);
    endfunction    
    
    // Write Method
    function void write(conv1_transaction tr);
        super.write(tr);
    endfunction                       
    
    // Predictor
    function predictor();   
        `uvm_info("SCB", "Start checking result..", UVM_NONE);
        `uvm_info("CONVWD_SCB", "INSERT PREDICTOR HERE", UVM_NONE);                   
    endfunction                                              
endclass                                                                