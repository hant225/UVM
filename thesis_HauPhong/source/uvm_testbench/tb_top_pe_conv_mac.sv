`timescale 1ns / 1ps
`include "uvm_macros.svh"
import uvm_pkg::*;
`include "test.sv"

//////////////////////////////////////////////////////////////////////////////////

interface pe_conv_mac_conv1_if();
    oper_mode     op;
    logic         clk;
    logic         rst;
    logic         en;
    logic         buffer_in_en;
    logic [71:0]  data_in;
    logic         load_weight;
    logic [31:0]  weight_addr;
    logic [63:0]  weight_data;
    logic [255:0] data_out;
    logic         done;
    logic         pe_ready;
    logic         valid;
endinterface

//////////////////////////////////////////////////////////////////////////////////

module tb_top_pe_conv_mac;
    // PARAMTERS
    parameter  pDATA_WIDTH        = 8;     
    parameter  pIN_CHANNEL        = 1;     
    parameter  pOUT_CHANNEL       = 32;    
    parameter  pKERNEL_SIZE       = 3;     
    parameter  pOUTPUT_PARALLEL   = 32;    
    parameter  pWEIGHT_DATA_WIDTH = 64;    
    parameter  pWEIGHT_BASE_ADDR  = 32'h4000_0000;     
    parameter  pACTIVATION        = "sigmoid";   
    
    // INSTANCES
    pe_conv_mac_conv1_if vif();                         // interface inst    
    
    pe_conv_mac_conv1 #(                                // DUT
         .pDATA_WIDTH         ( pDATA_WIDTH         )
        ,.pIN_CHANNEL         ( pIN_CHANNEL         )
        ,.pOUT_CHANNEL        ( pOUT_CHANNEL        )
        ,.pKERNEL_SIZE        ( pKERNEL_SIZE        )
        ,.pOUTPUT_PARALLEL    ( pOUTPUT_PARALLEL    )
        ,.pWEIGHT_BASE_ADDR   ( pWEIGHT_BASE_ADDR   )
        ,.pWEIGHT_DATA_WIDTH  ( pWEIGHT_DATA_WIDTH  )
        ,.pACTIVATION         ( pACTIVATION         )
    ) DUT (
         .clk           ( vif.clk          )
        ,.rst           ( vif.rst          )
        ,.en            ( vif.en           )
        ,.buffer_in_en  ( vif.buffer_in_en )
        ,.load_weight   ( vif.load_weight  )
        ,.weight_addr   ( vif.weight_addr  )
        ,.weight_data   ( vif.weight_data  )
        ,.data_in       ( vif.data_in      )
        ,.data_out      ( vif.data_out     )
        ,.pe_ready      ( vif.pe_ready     )
        ,.valid         ( vif.valid        )
        ,.done          ( vif.done         )    
    ); 
    
    bind pe_conv_mac_controller_conv1:pe_conv_mac_conv1.u_pe_controller SVA_pe_conv_mac_controller_conv1 dummy_ctrler (.*);     
    
    initial begin
        uvm_config_db #(virtual pe_conv_mac_conv1_if)::set(null, "*", "vif", vif);       
        run_test("test");
    end
    
    initial begin
        vif.clk = 1'b0;
    end
    
    always #10 vif.clk = ~vif.clk;
endmodule