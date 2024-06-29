`timescale 1ns / 1ps
`include "uvm_macros.svh"
import uvm_pkg::*;
import my_pkg::*;
`include "test.sv"

//////////////////////////////////////////////////////////////////////////////////

interface conv1_if();
    oper_mode op;
    logic                                clk;
    logic                                rst;
    logic                                en;        
    logic                                load_weight;
    logic [31:0]                         weight_addr;
    logic [pWEIGHT_DATA_WIDTH-1:0]       weight_data;
    logic [pDATA_WIDTH*pIN_CHANNEL-1:0]  data_in;
    logic [pDATA_WIDTH*pOUT_CHANNEL-1:0] data_out;
    logic                                valid;
    logic                                done;
endinterface

//////////////////////////////////////////////////////////////////////////////////

module top_tb_shuffle_net_conv1;
  
    // INSTANCES
    conv1_if vif();                         // interface inst
    logic tmp;
        
    IP_Conv1 #(                             // DUT
        .pDATA_WIDTH        (pDATA_WIDTH),    
        .pINPUT_WIDTH       (pINPUT_WIDTH),
        .pINPUT_HEIGHT      (pINPUT_HEIGHT),    
        .pWEIGHT_DATA_WIDTH (pWEIGHT_DATA_WIDTH),
        .pWEIGHT_BASE_ADDR  (pWEIGHT_BASE_ADDR),    
        .pIN_CHANNEL        (pIN_CHANNEL),
        .pOUT_CHANNEL       (pOUT_CHANNEL),    
        .pKERNEL_SIZE       (pKERNEL_SIZE),
        .pPADDING           (pPADDING),
        .pSTRIDE            (pSTRIDE),
        .pOUTPUT_PARALLEL   (pOUTPUT_PARALLEL),    
        .pACTIVATION        (pACTIVATION)
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
        run_test("test");
    end
    
endmodule
