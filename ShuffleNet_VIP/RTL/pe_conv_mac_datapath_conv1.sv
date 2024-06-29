`timescale 1ns/1ps

module pe_conv_mac_datapath_conv1 #(
   parameter  pDATA_WIDTH         = 8
   
  ,parameter  pIN_CHANNEL         = 3
  ,parameter  pOUT_CHANNEL        = 24
  
  ,parameter  pULTRA_RAM_NUM      = 3
  ,parameter  pBLOCK_RAM_NUM      = 4
  ,parameter  pKERNEL_NUM         = 27
  ,parameter  pBIAS_NUM           = 3
  
  ,parameter  pOUTPUT_PARALLEL    = 8
  
  // weights
  ,parameter  pWEIGHT_DATA_WIDTH  = 64
  ,parameter  pWEIGHT_BASE_ADDR   = 32'h4000_0000

  // activation type (relu, sigmoid)
  ,parameter  pACTIVATION         = "relu"
)(
   input  logic                                     clk
  ,input  logic                                     rst
  ,input  logic                                     clr
  ,input  logic                                     clr_weight
  
  ,input  logic                                     load_weight
  ,input  logic [31:0]                              weight_addr
  ,input  logic [pWEIGHT_DATA_WIDTH-1:0]            weight_data
  
  ,input  logic [$clog2(pKERNEL_NUM)-1:0]           kernel_addr
  ,input  logic [$clog2(pBIAS_NUM)-1:0]             bias_addr
  
  ,input  logic                                     en
  ,input  logic                                     adder_en
  ,input  logic                                     adder_en_weight
  ,input  logic                                     mul_en
  ,input  logic                                     sub_en
  ,input  logic                                     dequant_en
  ,input  logic                                     bias_en
  ,input  logic                                     act_en
  ,input  logic                                     quant_en
  
  ,input  logic [pDATA_WIDTH*pIN_CHANNEL-1:0]       data_in
  ,output logic [pDATA_WIDTH*pOUTPUT_PARALLEL-1:0]  data_out
);
  
  localparam pBIAS_BASE_ADDR = pWEIGHT_BASE_ADDR + pKERNEL_NUM;
  localparam pSCALE_ADDR = pBIAS_BASE_ADDR + pBIAS_NUM;
  localparam pSCALE_OUT_ADDR = pSCALE_ADDR + 1;

  // weights
  logic signed [pIN_CHANNEL*pOUTPUT_PARALLEL-1:0][pDATA_WIDTH-1:0] kernel_data;
  logic signed [pOUTPUT_PARALLEL-1:0][31:0] bias_data;
  logic signed [pOUTPUT_PARALLEL-1:0][63:0] dequant_scale_r;
  logic signed [63:0] scale_out;
  logic signed [pIN_CHANNEL-1:0][31:0] mac_out_weight [0:pOUTPUT_PARALLEL-1];
  logic signed [pIN_CHANNEL-1:0][31:0] mac_out [0:pOUTPUT_PARALLEL-1];
  
  logic signed [31:0] adder_out_weight [0:pOUTPUT_PARALLEL-1];  
  logic signed [31:0] adder_out [0:pOUTPUT_PARALLEL-1];
  
  logic signed [31:0] mul_out [0:pOUTPUT_PARALLEL-1];
  logic signed [31:0] sub_out [0:pOUTPUT_PARALLEL-1];
  
  logic signed [31:0] dequant_out [0:pOUTPUT_PARALLEL-1];
  logic signed [31:0] bias_out [0:pOUTPUT_PARALLEL-1];
  logic  [31:0] act_out [0:pOUTPUT_PARALLEL-1];
  logic  [7:0] quant_out [0:pOUTPUT_PARALLEL-1];   
  logic  [47:0] m_axis_dout_tdata [0:pOUTPUT_PARALLEL-1];   

  kernel_ram #(
     .pWEIGHT_DATA_WIDTH  ( pWEIGHT_DATA_WIDTH  )
    ,.pWEIGHT_BASE_ADDR   ( pWEIGHT_BASE_ADDR   )
    ,.pKERNEL_NUM         ( pKERNEL_NUM         )
    ,.pULTRA_RAM_NUM      ( pULTRA_RAM_NUM      )
  ) u_kernel (
     .clk         ( clk         )
    ,.rst         ( rst         )
    ,.wr_en       ( load_weight )
    ,.weight_addr ( weight_addr )
    ,.weight_data ( weight_data )
    ,.kernel_addr ( kernel_addr )
    ,.kernel_data ( kernel_data )
  );

  bias_ram #(
     .pWEIGHT_DATA_WIDTH  ( pWEIGHT_DATA_WIDTH  )
    ,.pWEIGHT_BASE_ADDR   ( pBIAS_BASE_ADDR     )
    ,.pBIAS_NUM           ( pBIAS_NUM           )
    ,.pBLOCK_RAM_NUM      ( pBLOCK_RAM_NUM      )
  ) u_bias (
     .clk         ( clk         )
    ,.rst         ( rst         )
    ,.wr_en       ( load_weight )
    ,.weight_addr ( weight_addr )
    ,.weight_data ( weight_data )
    ,.bias_addr   ( bias_addr   )
    ,.bias_data   ( bias_data   )
  );

  dequant_ram #(
     .pWEIGHT_DATA_WIDTH  ( pWEIGHT_DATA_WIDTH  )
    ,.pWEIGHT_BASE_ADDR   ( pSCALE_ADDR         )
    ,.pDEQUANT_SCALE_NUM  ( 1                   )
    ,.pBLOCK_RAM_NUM      ( pOUT_CHANNEL        )
  ) u_dequant_scale (
     .clk         ( clk         )
    ,.rst         ( rst         )
    ,.wr_en       ( load_weight )
    ,.weight_addr ( weight_addr )
    ,.weight_data ( weight_data )
    ,.dequant_scale_data   ( dequant_scale_r   )
  );
   
  always_ff @(posedge clk) begin
    if (load_weight && weight_addr == pSCALE_OUT_ADDR)
      scale_out <= weight_data;
  end
    
  genvar in_channel_idx;
  genvar out_channel_idx;
 
  generate

    for (out_channel_idx = 0; out_channel_idx < pOUTPUT_PARALLEL; out_channel_idx = out_channel_idx+1) begin
      if (out_channel_idx % 2 == 0) begin      
        for (in_channel_idx = 0; in_channel_idx < pIN_CHANNEL; in_channel_idx = in_channel_idx+1) begin  
          logic signed [15:0] dsp_out [0:1];
          logic mac_en;
          logic [2:0]cnt;       
          
          dsp_dual_mult_conv1 u_dsp (
             .clk       ( clk                                                         )
            ,.rst       ( rst                                                         )
            ,.en        ( en                                                          )
            ,.a         ( kernel_data[pIN_CHANNEL*out_channel_idx+in_channel_idx]     )
            ,.b         ( kernel_data[pIN_CHANNEL*(out_channel_idx+1)+in_channel_idx] )
            ,.c         ( data_in[pDATA_WIDTH*in_channel_idx +: pDATA_WIDTH]          )
            ,.ac        ( dsp_out[0]                                                  )
            ,.bc        ( dsp_out[1]                                                  )
            ,.valid_out ( mac_en                                                      )
          );
          
          always_ff @(posedge clk) begin
            if (rst || clr) begin
              mac_out[out_channel_idx][in_channel_idx] <= 'b0;
              mac_out[out_channel_idx+1][in_channel_idx] <= 'b0;
            end
            else if (mac_en) begin
              mac_out[out_channel_idx][in_channel_idx] <= mac_out[out_channel_idx][in_channel_idx] + {{16{dsp_out[0][15]}}, dsp_out[0]};
              mac_out[out_channel_idx+1][in_channel_idx] <= mac_out[out_channel_idx+1][in_channel_idx] + {{16{dsp_out[1][15]}}, dsp_out[1]};
            end
          end // always 
          
          always_ff @(posedge clk) begin 
            if (rst) begin
              cnt <= 'b0;
            end
            else if (en) begin
              if( cnt >= 9)
                cnt <= 'b0;
              else
                cnt <= cnt + 1;
            end
          end
          
          always_ff @(posedge clk) begin
            if (rst || clr_weight) begin
              mac_out_weight[out_channel_idx][in_channel_idx] <= 'b0;
              mac_out_weight[out_channel_idx+1][in_channel_idx] <= 'b0;
            end
            else if (en && data_in[pDATA_WIDTH*in_channel_idx +: pDATA_WIDTH] != 0 && cnt < 9) begin
              mac_out_weight[out_channel_idx][in_channel_idx] <= mac_out_weight[out_channel_idx][in_channel_idx] + {{24{kernel_data[pIN_CHANNEL*out_channel_idx+in_channel_idx][7]}},kernel_data[pIN_CHANNEL*out_channel_idx+in_channel_idx]};
              mac_out_weight[out_channel_idx+1][in_channel_idx] <= mac_out_weight[out_channel_idx+1][in_channel_idx] + {{24{kernel_data[pIN_CHANNEL*(out_channel_idx+1)+in_channel_idx][7]}},kernel_data[pIN_CHANNEL*(out_channel_idx+1)+in_channel_idx]};
            end
          end // always 
                          
        end // for in_channel_idx
      end // if out_channel_idx % 2 == 0

      adder_tree #(
         .pDATA_WIDTH ( 32          )
        ,.pINPUT_NUM  ( pIN_CHANNEL ) 
      ) u_adder_tree_weight (
         .clk       ( clk                         )
        ,.rst       ( rst                         )
        ,.en        ( adder_en_weight                    )
        ,.data_in   ( mac_out_weight[out_channel_idx]    )
        ,.data_out  ( adder_out_weight[out_channel_idx]  )
      );

      always_ff @(posedge clk) begin
        if (rst)
          mul_out[out_channel_idx] <= 'b0;
        else if (mul_en)
          mul_out[out_channel_idx] <= adder_out_weight[out_channel_idx]*57;
      end

      always_ff @(posedge clk) begin
        if (rst)
          sub_out[out_channel_idx] <= 'b0;
        else if (sub_en)
          sub_out[out_channel_idx] <= adder_out[out_channel_idx] - mul_out[out_channel_idx];
      end
                      
      adder_tree #(
         .pDATA_WIDTH ( 32          )
        ,.pINPUT_NUM  ( pIN_CHANNEL ) 
      ) u_adder_tree (
         .clk       ( clk                         )
        ,.rst       ( rst                         )
        ,.en        ( adder_en                    )
        ,.data_in   ( mac_out[out_channel_idx]    )
        ,.data_out  ( adder_out[out_channel_idx]  )
      );
    
      dequantize u_dequantize (
         .clk       ( clk                                            )
        ,.rst       ( rst                                            )
        ,.en        ( dequant_en                                     )
        ,.scale     ( dequant_scale_r[out_channel_idx][31:0]         )
        ,.data_in   ( sub_out[out_channel_idx]                       )
        ,.data_out  ( dequant_out[out_channel_idx]                   )
      );
  
      always_ff @(posedge clk) begin
        if (rst)
          bias_out[out_channel_idx] <= 'b0;
        else if (bias_en)
          bias_out[out_channel_idx] <= dequant_out[out_channel_idx] + bias_data[out_channel_idx];
      end
      
      if (pACTIVATION == "sigmoid")
        sigmoid #(
           .pDATA_WIDTH ( 32  )
          ,.pFRAC_NUM   ( 16  )
        ) u_sigmoid (
           .clk       ( clk                       )
          ,.rst       ( rst                       )
          ,.en        ( act_en                    )
          ,.data_in   ( bias_out[out_channel_idx] )
          ,.data_out  ( act_out[out_channel_idx]  )
        );
      else if (pACTIVATION == "relu")
        relu #(
           .pDATA_WIDTH ( 32  )
        ) u_relu (
           .clk       ( clk                       )
          ,.rst       ( rst                       )
          ,.en        ( act_en                    )
          ,.data_in   ( bias_out[out_channel_idx] )
          ,.data_out  ( act_out[out_channel_idx]  )
        );
      else
      always_ff @(posedge clk) begin
        if (rst)
          act_out[out_channel_idx] <= 'b0;
        else
          act_out[out_channel_idx] <= bias_out[out_channel_idx];
      end


      div_gen_0 u_dequant (
        .aclk                   ( clk                               ),  // input wire aclk
        .aresetn                ( !rst                              ),  // input wire aresetn
        .s_axis_divisor_tvalid  ( quant_en                          ),  // input wire s_axis_divisor_tvalid
        .s_axis_divisor_tdata   ( scale_out[47:16]                  ),  // input wire [31 : 0] s_axis_divisor_tdata
        .s_axis_dividend_tvalid ( quant_en                          ),  // input wire s_axis_dividend_tvalid
        .s_axis_dividend_tdata  ( act_out[out_channel_idx]          ),  // input wire [31 : 0] s_axis_dividend_tdata
        .m_axis_dout_tvalid     ( m_axis_dout_tvalid                ),  // output wire m_axis_dout_tvalid
        .m_axis_dout_tdata      ( m_axis_dout_tdata[out_channel_idx])   // output wire [47 : 0] m_axis_dout_tdata
      ); 
      
      assign quant_out[out_channel_idx]= m_axis_dout_tdata[out_channel_idx][23:16]; 
      assign data_out[out_channel_idx*pDATA_WIDTH +: pDATA_WIDTH] = quant_out[out_channel_idx];
    end // for out_channel_idx
  endgenerate
    
endmodule