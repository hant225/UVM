`timescale 1ns / 1ps

module pe_conv_mac_conv1 #(
   parameter  pDATA_WIDTH         = 8
   
  ,parameter  pIN_CHANNEL         = 3
  ,parameter  pOUT_CHANNEL        = 24
  
  ,parameter  pKERNEL_SIZE        = 3
  
  ,parameter  pOUTPUT_PARALLEL    = 8
  
  ,parameter  pWEIGHT_DATA_WIDTH  = 64
  ,parameter  pWEIGHT_BASE_ADDR   = 32'h4000_0000
  
  ,parameter  pINPUT_WIDTH  = 224
  ,parameter  pINPUT_HEIGHT = 224
  ,parameter  pPADDING      = 1
  ,parameter  pSTRIDE       = 2  
  // activation type (relu, sigmoid)
  ,parameter  pACTIVATION         = "relu"
)(
   input  logic                                                         clk
  ,input  logic                                                         rst
  
  ,input  logic                                                         load_weight
  ,input  logic [31:0]                                                  weight_addr
  ,input  logic [pWEIGHT_DATA_WIDTH-1:0]                                weight_data
  
  ,input  logic                                                         buffer_in_en
  ,input  logic                                                         en
  ,input  logic [pDATA_WIDTH*pIN_CHANNEL*pKERNEL_SIZE*pKERNEL_SIZE-1:0] data_in
  ,output logic [pDATA_WIDTH*pOUT_CHANNEL-1:0]                          data_out
  
  ,output logic                                                         padding_slot
  ,output logic                                                         pe_ready
  ,output logic                                                         valid
  ,output logic                                                         done
);

  localparam pDSP_NUM = pIN_CHANNEL * pOUTPUT_PARALLEL;
  localparam pULTRA_RAM_NUM = pDSP_NUM/8;
  localparam pBLOCK_RAM_NUM = pOUTPUT_PARALLEL/2;
  localparam pKERNEL_NUM = 9*(pOUT_CHANNEL/pOUTPUT_PARALLEL);
  localparam pBIAS_NUM = (pOUT_CHANNEL/pOUTPUT_PARALLEL);
  
  logic [$clog2(pOUT_CHANNEL/pOUTPUT_PARALLEL)-1:0] buffer_idx;
  logic [$clog2(pKERNEL_NUM)-1:0] kernel_addr;
  logic [$clog2(pBIAS_NUM)-1:0] bias_addr;
  logic [$clog2(pKERNEL_SIZE*pKERNEL_SIZE)-1:0] pixel;
  logic [pDATA_WIDTH*pIN_CHANNEL-1:0] buffer_out;
  logic [pDATA_WIDTH*pIN_CHANNEL-1:0] datapath_in;
  logic [pDATA_WIDTH*pOUTPUT_PARALLEL-1:0] datapath_out;
  
  logic datapath_en;
  logic datapath_main_en;

  logic buffer_valid;
  logic pe_clr;
  logic datapath_buffer_en;
  logic adder_en;
  logic dequant_en;
  logic bias_en;
  logic act_en;
  logic quant_en;
  logic buffer_en;
  
  assign datapath_in = datapath_buffer_en ? 'b0 : buffer_out;

  always_ff @(posedge clk) begin
    if (rst)
      datapath_en <= 'b0;
    else
      datapath_en <= en;    
  end

  always_ff @(posedge clk) begin
    if (rst)
      datapath_main_en <= 'b0;
    else
      datapath_main_en <= datapath_en;  
  end
    
  pe_conv_mac_controller_conv1 #(
     .pIN_CHANNEL       ( pIN_CHANNEL       )
    ,.pOUT_CHANNEL      ( pOUT_CHANNEL      )
    ,.pKERNEL_SIZE      ( pKERNEL_SIZE      )
    ,.pOUTPUT_PARALLEL  ( pOUTPUT_PARALLEL  )
    ,.pKERNEL_NUM       ( pKERNEL_NUM       )
    ,.pBIAS_NUM         ( pBIAS_NUM         )
    ,.pACTIVATION       ( pACTIVATION       )
    ,.pINPUT_WIDTH      ( pINPUT_WIDTH      )
    ,.pINPUT_HEIGHT     ( pINPUT_HEIGHT     )
    ,.pPADDING          ( pPADDING          )
    ,.pSTRIDE           ( pSTRIDE           )    
  ) u_pe_controller (
     .clk                 ( clk                 )
    ,.rst                 ( rst                 )
    ,.en                  ( en                  )
    ,.buffer_valid        ( buffer_valid        )
    ,.buffer_idx          ( buffer_idx          )
    ,.pixel               ( pixel               )
    ,.kernel_addr         ( kernel_addr         )
    ,.bias_addr           ( bias_addr           )
    ,.pe_ready            ( pe_ready            )
    ,.pe_clr              ( pe_clr              )
    ,.clr_weight          ( clr_weight          )
    ,.mul_en              ( mul_en              )
    ,.sub_en              ( sub_en              )
    ,.datapath_buffer_en  ( datapath_buffer_en  )
    ,.adder_en            ( adder_en            )
    ,.adder_en_weight     ( adder_en_weight     )
    ,.dequant_en          ( dequant_en          )
    ,.bias_en             ( bias_en             )
    ,.act_en              ( act_en              )
    ,.quant_en            ( quant_en            )
    ,.buffer_en           ( buffer_en           )
    ,.valid               ( valid               )
    ,.done                ( done                )    
  );

  pe_conv_mac_buffer_in_conv1 #(
     .pDATA_WIDTH   ( pDATA_WIDTH*pIN_CHANNEL )
    ,.pKERNEL_SIZE  ( pKERNEL_SIZE            )
  ) u_pe_buffer_in (
     .clk         ( clk           )
    ,.rst         ( rst           )
    ,.en          ( buffer_in_en  )
    ,.pixel       ( pixel         )
    ,.data_in     ( data_in       )
    ,.data_out    ( buffer_out    )    
    ,.valid       ( buffer_valid  )
  );
  
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
  ) u_pe_datapath (
     .clk         ( clk           )
    ,.rst         ( rst           )
    ,.clr         ( pe_clr        )
    ,.clr_weight  ( clr_weight    )
    ,.load_weight ( load_weight   )
    ,.weight_addr ( weight_addr   )
    ,.weight_data ( weight_data   )
    ,.kernel_addr ( kernel_addr   )
    ,.bias_addr   ( bias_addr     )
    ,.en          ( datapath_main_en   )
    ,.adder_en    ( adder_en      )
    ,.adder_en_weight( adder_en_weight )
    ,.mul_en      ( mul_en )
    ,.sub_en      ( sub_en )
    ,.dequant_en  ( dequant_en    )
    ,.bias_en     ( bias_en       )
    ,.act_en      ( act_en        )
    ,.quant_en    ( quant_en      )
    ,.data_in     ( datapath_in   )
    ,.data_out    ( datapath_out  )
  );
  
  pe_conv_mac_buffer_out_conv1 #(
     .pDATA_WIDTH       ( pDATA_WIDTH       )
    ,.pOUT_CHANNEL      ( pOUT_CHANNEL      )
    ,.pOUTPUT_PARALLEL  ( pOUTPUT_PARALLEL  )
  ) u_pe_buffer_out (
     .clk         ( clk           )
    ,.rst         ( rst           )
    ,.wr_en       ( buffer_en     )
    ,.buffer_idx  ( buffer_idx    )
    ,.data_in     ( datapath_out  )
    ,.data_out    ( data_out      )
  );
  
endmodule