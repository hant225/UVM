`timescale 1ns / 1ps
`include "conv1_test.sv"
`include "uvm_macros.svh"
import uvm_pkg::*;
import conv1_pkg::*;            
          
//////////////////////////////////////////////////////////////////////////////////

interface conv1_if();
    oper_mode op;
    logic                                                      clk;
    logic                                                      rst;
    logic                                                      en;        
    logic                                                      load_weight;
    logic [31:0]                                               weight_addr;
    logic [conv1_pkg::pWEIGHT_DATA_WIDTH-1:0]                  weight_data;
    logic [conv1_pkg::pDATA_WIDTH*conv1_pkg::pIN_CHANNEL-1:0]  data_in;
    logic [conv1_pkg::pDATA_WIDTH*conv1_pkg::pOUT_CHANNEL-1:0] data_out;
    logic                                                      valid;
    logic                                                      done;
endinterface

//////////////////////////////////////////////////////////////////////////////////

interface convDW_if();
    oper_mode op;
    logic                                                        clk;
    logic                                                        rst;
    logic                                                        en;        
    logic                                                        load_weight;
    logic [31:0]                                                 weight_addr;
    logic [convDW_pkg::pWEIGHT_DATA_WIDTH-1:0]                   weight_data;
    logic [convDW_pkg::pDATA_WIDTH*convDW_pkg::pIN_CHANNEL-1:0]  data_in;
    logic [convDW_pkg::pDATA_WIDTH*convDW_pkg::pOUT_CHANNEL-1:0] data_out;
    logic                                                        valid;
    logic                                                        done;
endinterface

//////////////////////////////////////////////////////////////////////////////////

module conv1_top_tb;
  
    // INSTANCES
    conv1_if vif();                         // interface inst
    logic tmp;
        
    IP_Conv1 #(                             // DUT
        .pDATA_WIDTH        (conv1_pkg::pDATA_WIDTH),    
        .pINPUT_WIDTH       (conv1_pkg::pINPUT_WIDTH),
        .pINPUT_HEIGHT      (conv1_pkg::pINPUT_HEIGHT),    
        .pWEIGHT_DATA_WIDTH (conv1_pkg::pWEIGHT_DATA_WIDTH),
        .pWEIGHT_BASE_ADDR  (conv1_pkg::pWEIGHT_BASE_ADDR),    
        .pIN_CHANNEL        (conv1_pkg::pIN_CHANNEL),
        .pOUT_CHANNEL       (conv1_pkg::pOUT_CHANNEL),    
        .pKERNEL_SIZE       (conv1_pkg::pKERNEL_SIZE),
        .pPADDING           (conv1_pkg::pPADDING),
        .pSTRIDE            (conv1_pkg::pSTRIDE),
        .pOUTPUT_PARALLEL   (conv1_pkg::pOUTPUT_PARALLEL),    
        .pACTIVATION        (conv1_pkg::pACTIVATION)
    ) DUT (    
        .clk         (vif.clk),
        .rst         (vif.rst),
        .en          (vif.en),
        .load_weight (vif.load_weight),
        .weight_addr (vif.weight_addr),
        .weight_data (vif.weight_data),
        .data_in     (vif.data_in),    
        .data_out    (vif.data_out),
        .valid       (vif.valid),
        .done        (vif.done)
    );
    
    initial begin
        vif.clk = 1'b0;
    end
    
    always #10 vif.clk = ~vif.clk;
    
    initial begin
        uvm_config_db #(virtual conv1_if)::set(null, "*", "vif", vif);
        run_test("conv1_test");
    end
    
endmodule