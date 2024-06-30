`timescale 1ns / 1ps
//////////////////////////////////////////////////////////////////////////////////
// Company: 
// Engineer: 
// 
// Create Date: 04/10/2024 12:31:38 AM
// Design Name: 
// Module Name: IP_ConvDW
// Project Name: 
// Target Devices: 
// Tool Versions: 
// Description: 
// 
// Dependencies: 
// 
// Revision:
// Revision 0.01 - File Created
// Additional Comments:
// 
//////////////////////////////////////////////////////////////////////////////////


module IP_Conv1 #(
  parameter pDATA_WIDTH    = 8

  ,parameter pINPUT_WIDTH   = 224
  ,parameter pINPUT_HEIGHT  = 224
  
  ,parameter pWEIGHT_DATA_WIDTH = 64
  ,parameter pWEIGHT_BASE_ADDR  = 32'h4000_0000
  
  ,parameter pIN_CHANNEL  = 3
  ,parameter pOUT_CHANNEL = 24
  
  ,parameter pKERNEL_SIZE = 3
  ,parameter pPADDING     = 1
  ,parameter pSTRIDE      = 2
  ,parameter pOUTPUT_PARALLEL = 8
  
  ,parameter pACTIVATION  = "relu"
)(

  input wire clk,
  input wire rst,
  input wire en,
  input logic load_weight,
  input logic [31:0] weight_addr,
  input logic [pWEIGHT_DATA_WIDTH-1:0] weight_data,
  input wire [pDATA_WIDTH*pIN_CHANNEL-1:0] data_in,
  
  output logic [pDATA_WIDTH*pOUT_CHANNEL-1:0] data_out,
  output logic valid,
  output logic done
);
  
  wire [pDATA_WIDTH*pIN_CHANNEL-1:0] fifo_out;
  wire fifo_empty;
  wire fifo_valid;
  wire rd_en;
  wire [15:0]data_count;
  wire full;

  fifo_width24 fifo (
  .clk(clk),                // input wire clk
  .srst(rst),              // input wire srst
  .din(data_in),                // input wire [23 : 0] din
  .wr_en(en),            // input wire wr_en
  .rd_en(rd_en),            // input wire rd_en
  .dout(fifo_out),              // output wire [23 : 0] dout
  .full(full),              // output wire full
  .empty(fifo_empty),            // output wire empty
  .valid(fifo_valid),            // output wire valid
  .data_count(data_count)  // output wire [15 : 0] data_count
  );  
      
  Conv1 #(
     .pDATA_WIDTH         ( pDATA_WIDTH         )
    ,.pINPUT_WIDTH        ( pINPUT_WIDTH        )
    ,.pINPUT_HEIGHT       ( pINPUT_HEIGHT       )
    ,.pIN_CHANNEL         ( pIN_CHANNEL         )
    ,.pOUT_CHANNEL        ( pOUT_CHANNEL        )
    ,.pKERNEL_SIZE        ( pKERNEL_SIZE        )
    ,.pPADDING            ( pPADDING            )
    ,.pSTRIDE             ( pSTRIDE             )
    ,.pOUTPUT_PARALLEL    ( pOUTPUT_PARALLEL    )
    ,.pWEIGHT_DATA_WIDTH  ( pWEIGHT_DATA_WIDTH  )
    ,.pWEIGHT_BASE_ADDR   ( pWEIGHT_BASE_ADDR   )
    ,.pACTIVATION         ( pACTIVATION         )
  ) u_conv1 (
     .clk         ( clk         )
    ,.rst         ( rst         )
    ,.en          ( !fifo_empty )
    ,.load_weight ( load_weight )
    ,.weight_addr ( weight_addr )
    ,.weight_data ( weight_data )
    ,.rd_en       ( rd_en       )
    ,.data_valid  ( fifo_valid  )
    ,.data_in     ( fifo_out    )
    ,.data_out    ( data_out    )
    ,.valid       ( valid       )
    ,.done        ( done        )
  );    

endmodule