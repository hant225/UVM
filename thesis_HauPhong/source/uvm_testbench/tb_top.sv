`timescale 1ns / 1ps
`include "uvm_macros.svh"
import uvm_pkg::*;
`include "test.sv"

//////////////////////////////////////////////////////////////////////////////////

interface pe_conv_mac_datapath_if();
  oper_mode op;

  logic         clk;
  logic         rst;
  logic         clr;
  logic         load_weight;
  logic [31:0]  weight_addr;
  logic [63:0]  weight_data;
  logic [3:0]   kernel_addr;
  logic [4:0]   bias_addr;
  logic         en;
  logic         adder_en;
  logic         dequant_en;
  logic         bias_en;
  logic         act_en;
  logic         quant_en;
  logic [7:0]   data_in;
  logic [255:0] data_out;
endinterface

//////////////////////////////////////////////////////////////////////////////////

module tb_top;
    parameter  pDATA_WIDTH         = 8;
    parameter  pIN_CHANNEL         = 1;
    parameter  pOUT_CHANNEL        = 32;
    parameter  pKERNEL_SIZE        = 3;
    parameter  pOUTPUT_PARALLEL    = 32;
    parameter  pWEIGHT_DATA_WIDTH  = 64;
    parameter  pWEIGHT_BASE_ADDR   = 32'h4000_0000;
    parameter  pINPUT_WIDTH        = 28;
    parameter  pINPUT_HEIGHT       = 28;
    parameter  pPADDING            = 1;
    parameter  pSTRIDE             = 1 ;
    parameter  pACTIVATION         = "sigmoid";
    localparam pDSP_NUM       = pIN_CHANNEL * pOUTPUT_PARALLEL;                 // 32
    localparam pULTRA_RAM_NUM = pDSP_NUM / (pWEIGHT_DATA_WIDTH/pDATA_WIDTH);    // 4
    localparam pBLOCK_RAM_NUM = pOUTPUT_PARALLEL/2;                             // 16
    localparam pKERNEL_NUM    = pIN_CHANNEL*pOUT_CHANNEL*pKERNEL_SIZE*pKERNEL_SIZE*pDATA_WIDTH/pWEIGHT_DATA_WIDTH/pULTRA_RAM_NUM;   // 1 x 32 x 3**2 x 8 / 64 / 4 = 9 
    localparam pBIAS_NUM      = (pOUT_CHANNEL == pOUTPUT_PARALLEL) ? pOUT_CHANNEL/2 : pOUT_CHANNEL/pOUTPUT_PARALLEL;                // 32 / 2 = 16
    
    pe_conv_mac_datapath_if vif();
    pe_conv_mac_datapath_conv1 #(
         .pDATA_WIDTH         ( pDATA_WIDTH         )
        ,.pIN_CHANNEL         ( pIN_CHANNEL         )
        ,.pOUT_CHANNEL        ( pOUT_CHANNEL        )
        ,.pULTRA_RAM_NUM      ( pULTRA_RAM_NUM      )
        ,.pBLOCK_RAM_NUM      ( pBLOCK_RAM_NUM      )
        ,.pKERNEL_NUM         ( pKERNEL_NUM         )
        ,.pBIAS_NUM           ( pBIAS_NUM           )
        ,.pOUTPUT_PARALLEL    ( pOUTPUT_PARALLEL    )
        ,.pWEIGHT_DATA_WIDTH  ( pWEIGHT_DATA_WIDTH  )
        ,.pWEIGHT_BASE_ADDR   ( pWEIGHT_BASE_ADDR   )
     ) DUT (
         .clk         (vif.clk           )
        ,.rst         (vif.rst           )
        ,.clr         (vif.clr        )
        ,.load_weight (vif.load_weight   )
        ,.weight_addr (vif.weight_addr   )
        ,.weight_data (vif.weight_data   )
        ,.kernel_addr (vif.kernel_addr   )
        ,.bias_addr   (vif.bias_addr     )
        ,.en          (vif.en   )
        ,.adder_en    (vif.adder_en      )
        ,.dequant_en  (vif.dequant_en    )
        ,.bias_en     (vif.bias_en       )
        ,.act_en      (vif.act_en        )
        ,.quant_en    (vif.quant_en      )
        ,.data_in     (vif.data_in   )
        ,.data_out    (vif.data_out  )
      );
    
    
    
    initial begin
        uvm_config_db #(virtual pe_conv_mac_datapath_if)::set(null, "*", "vif", vif);       
        run_test("test");
    end
    
    initial begin
        vif.clk = 1'b0;
    end
    
    always #10 vif.clk = ~vif.clk;
endmodule
