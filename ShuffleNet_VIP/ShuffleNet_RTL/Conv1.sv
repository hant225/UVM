`timescale 1ns/1ps

module Conv1 #(
   parameter  pDATA_WIDTH         = 8
   
  ,parameter  pINPUT_WIDTH        = 224
  ,parameter  pINPUT_HEIGHT       = 224
  
  ,parameter  pIN_CHANNEL         = 3
  ,parameter  pOUT_CHANNEL        = 24
  
  ,parameter  pKERNEL_SIZE        = 3
  ,parameter  pPADDING            = 1
  ,parameter  pSTRIDE             = 2
  
  ,parameter  pOUTPUT_PARALLEL    = 8
  
  // kernel ram
  ,parameter  pWEIGHT_DATA_WIDTH  = 64
  ,parameter  pWEIGHT_BASE_ADDR   = 0
  
  // activation type (sigmoid, relu)
  ,parameter  pACTIVATION   = "relu"
)(
   input  logic                                 clk
  ,input  logic                                 rst
  ,input  logic                                 en
  ,input  logic                                 load_weight
  ,input  logic [31:0]                          weight_addr
  ,input  logic [pWEIGHT_DATA_WIDTH-1:0]        weight_data
  ,input  logic                                 data_valid
  ,input  logic [pDATA_WIDTH*pIN_CHANNEL-1:0]   data_in
  ,output logic [pDATA_WIDTH*pOUT_CHANNEL-1:0]  data_out
  ,output logic                                 rd_en
  ,output logic                                 valid
  ,output logic                                 done
);

  localparam pWINDOW_SIZE = pKERNEL_SIZE * pKERNEL_SIZE;
  
  logic [pDATA_WIDTH*pIN_CHANNEL-1:0] buffer_in;
  logic [pDATA_WIDTH*pIN_CHANNEL*pWINDOW_SIZE-1:0] buffer_out;
  logic is_padding;
  logic padding_valid;
  logic buffer_en;
  logic pe_en;
  logic pe_ready;
   
  assign buffer_in = padding_valid ? 'b0 : data_in;
  
  always_ff @(posedge clk) begin
    if (rst)
      padding_valid <= 'b0;
    else
      padding_valid <= is_padding;
  end
  
  cnn_controller_conv1 #(
     .pINPUT_WIDTH  ( pINPUT_WIDTH  )
    ,.pINPUT_HEIGHT ( pINPUT_HEIGHT )
    ,.pKERNEL_SIZE  ( pKERNEL_SIZE  )
    ,.pPADDING      ( pPADDING      )
    ,.pSTRIDE       ( pSTRIDE       )
  ) u_controller (
     .clk         ( clk                         )
    ,.rst         ( rst                         )
    ,.en          ( en                          )
    ,.rd_en       ( rd_en                       )
    ,.data_valid  ( data_valid || padding_valid )
    ,.is_padding  ( is_padding                  )
    ,.buffer_en   ( buffer_en                   )
    ,.pe_en       ( pe_en                       )
    ,.pe_ready    ( pe_ready                    )
    ,.valid_one   ( pe_en && (data_valid || padding_valid)                        )
    
  );
      
  cnn_buffer_conv1 #(
     .pINPUT_WIDTH  ( pINPUT_WIDTH            )
    ,.pDATA_WIDTH   ( pDATA_WIDTH*pIN_CHANNEL )
    ,.pKERNEL_SIZE  ( pKERNEL_SIZE            )
    ,.pPADDING      ( pPADDING                )
  ) u_buffer (
     .clk       ( clk         )
    ,.rst       ( rst         )
    ,.en        ( buffer_en   )
    ,.data_in   ( buffer_in   )
    ,.data_out  ( buffer_out  )
  );

  pe_conv_mac_conv1 #(
     .pDATA_WIDTH         ( pDATA_WIDTH         )
    ,.pIN_CHANNEL         ( pIN_CHANNEL         )
    ,.pOUT_CHANNEL        ( pOUT_CHANNEL        )
    ,.pKERNEL_SIZE        ( pKERNEL_SIZE        )
    ,.pOUTPUT_PARALLEL    ( pOUTPUT_PARALLEL    )
    ,.pWEIGHT_BASE_ADDR   ( pWEIGHT_BASE_ADDR   )
    ,.pWEIGHT_DATA_WIDTH  ( pWEIGHT_DATA_WIDTH  )
    ,.pACTIVATION         ( pACTIVATION         )
    ,.pINPUT_WIDTH        ( pINPUT_WIDTH        )
    ,.pINPUT_HEIGHT       ( pINPUT_HEIGHT       )
    ,.pPADDING            ( pPADDING            )
    ,.pSTRIDE             ( pSTRIDE             )
  ) u_pe (
     .clk           ( clk                 )
    ,.rst           ( rst                 )
    ,.en            ( pe_en               )
    ,.buffer_in_en  ( buffer_en && pe_en  )
    ,.load_weight   ( load_weight         )
    ,.weight_addr   ( weight_addr         )
    ,.weight_data   ( weight_data         )
    ,.data_in       ( buffer_out          )
    ,.data_out      ( data_out            )
    ,.pe_ready      ( pe_ready            )
    ,.valid         ( valid               )
    ,.done          ( done                )    
  );   
        
endmodule