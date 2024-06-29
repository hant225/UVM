`timescale 1ns/1ps

module pe_conv_mac_controller_conv1 #(   
   parameter  pIN_CHANNEL       = 3
  ,parameter  pOUT_CHANNEL      = 24
  ,parameter  pKERNEL_SIZE      = 3
  
  ,parameter  pOUTPUT_PARALLEL  = 8
    
  ,parameter  pKERNEL_NUM       = 27     // 9*(pOUT_CHANNEL/pOUTPUT_PARALLEL)
  ,parameter  pBIAS_NUM         = 3     // pOUT_CHANNEL/pOUTPUT_PARALLEL

  ,parameter  pINPUT_WIDTH  = 224
  ,parameter  pINPUT_HEIGHT = 224
  ,parameter  pPADDING      = 1
  ,parameter  pSTRIDE       = 2  
  
  // activation type (relu, sigmoid)
  ,parameter  pACTIVATION         = "relu"
)(
   input  logic                                             clk
  ,input  logic                                             rst
  ,input  logic                                             en
  ,input  logic                                             buffer_valid
  ,output logic [$clog2(pKERNEL_SIZE*pKERNEL_SIZE)-1:0]     pixel
  ,output logic [$clog2(pKERNEL_NUM)-1:0]                   kernel_addr
  ,output logic [$clog2(pBIAS_NUM)-1:0]                     bias_addr
  ,output logic [$clog2(pOUT_CHANNEL/pOUTPUT_PARALLEL)-1:0] buffer_idx
  ,output logic                                             pe_ready
  ,output logic                                             pe_clr
  ,output logic                                             clr_weight
  ,output logic                                             mul_en
  ,output logic                                             sub_en
  ,output logic                                             datapath_buffer_en
  ,output logic                                             adder_en
  ,output logic                                             adder_en_weight
  ,output logic                                             dequant_en
  ,output logic                                             bias_en
  ,output logic                                             act_en
  ,output logic                                             quant_en
  ,output logic                                             buffer_en
  ,output logic                                             valid
  ,output logic                                             done
);

  localparam pSUB_PIPE_STAGE_NUM      = 1; 
  localparam pPE_CLR_STAGE_NUM        = 1; 
  localparam pMAC_PIPE_STAGE_NUM      = 8;
  localparam pDEQUANT_PIPE_STAGE_NUM  = 9;
  localparam pBIAS_PIPE_STAGE_NUM     = 1;
  localparam pQUANT_PIPE_STAGE_NUM    = 52;
  localparam pSIGMOID_PIPE_STAGE_NUM  = 4;
  localparam pRELU_PIPE_STAGE_NUM     = 1;
  
  localparam pADDER_PIPE_STAGE_NUM = $clog2(pIN_CHANNEL) + 1;
  localparam pACT_PIPE_STAGE_NUM =  pACTIVATION == "sigmoid"  ? pSIGMOID_PIPE_STAGE_NUM :
                                    pACTIVATION == "relu"     ? pRELU_PIPE_STAGE_NUM    : 'b0;
  localparam pPIPE_STAGE_NUM = pMAC_PIPE_STAGE_NUM + pADDER_PIPE_STAGE_NUM + pSUB_PIPE_STAGE_NUM + pDEQUANT_PIPE_STAGE_NUM +
                               pBIAS_PIPE_STAGE_NUM + pACT_PIPE_STAGE_NUM + pQUANT_PIPE_STAGE_NUM + 1;
  
  localparam pADDER_STAGE_NUM   = pMAC_PIPE_STAGE_NUM;
  localparam pSUB_STAGE_NUM     = pADDER_STAGE_NUM  + pADDER_PIPE_STAGE_NUM;
  localparam pDEQUAN_STAGE_NUM  = pSUB_STAGE_NUM  + pSUB_PIPE_STAGE_NUM;
  localparam pBIAS_STAGE_NUM    = pDEQUAN_STAGE_NUM + pDEQUANT_PIPE_STAGE_NUM;
  localparam pACT_STAGE_NUM     = pBIAS_STAGE_NUM   + pBIAS_PIPE_STAGE_NUM;
  localparam pQUANT_STAGE_NUM   = pACT_STAGE_NUM    + pACT_PIPE_STAGE_NUM;
  localparam pBUFFER_STAGE_NUM  = pQUANT_STAGE_NUM  + pQUANT_PIPE_STAGE_NUM;
  localparam pVALID_STAGE_NUM   = pBUFFER_STAGE_NUM + 1; 

  logic [$clog2(pOUT_CHANNEL/pOUTPUT_PARALLEL)-1:0] out_channel;
  logic [$clog2(pKERNEL_SIZE*pKERNEL_SIZE+pMAC_PIPE_STAGE_NUM-1):0] cntr_r;
  logic [pPIPE_STAGE_NUM-1:0] valid_r;
  logic pixel_en;
  logic pe_busy;
  

  localparam pOUT_WIDTH = (pINPUT_WIDTH - pKERNEL_SIZE + 2*pPADDING)/pSTRIDE + 1;
  localparam pOUT_HEIGHT = (pINPUT_HEIGHT - pKERNEL_SIZE + 2*pPADDING)/pSTRIDE + 1;
  logic [$clog2(pOUT_WIDTH * pOUT_HEIGHT * (pOUT_CHANNEL/pOUTPUT_PARALLEL)):0]count_valid;
  
    
  genvar reg_idx;
  
  generate
    for (reg_idx = 0; reg_idx < pPIPE_STAGE_NUM; reg_idx = reg_idx+1) begin
      logic valid_in;
      
      assign valid_in = reg_idx ? valid_r[reg_idx-1] : cntr_r == pKERNEL_SIZE*pKERNEL_SIZE-1 && en; 
        
      always_ff @(posedge clk) begin
        if (rst)
          valid_r[reg_idx] <= 'b0;
        else
          valid_r[reg_idx] <= valid_in;
      end   
    end
  endgenerate
  
//logic valid_in[0:3]; // Adjust the array size based on the actual number of stages

//// Initial stage
//assign valid_in[0] = cntr_r == pKERNEL_SIZE*pKERNEL_SIZE-1 && en;

//// Pipeline stages
//always_ff @(posedge clk) begin
//  if (rst) begin
//    valid_r[0] <= 'b0;
//    valid_r[1] <= 'b0;
//    valid_r[2] <= 'b0;
//    valid_r[3] <= 'b0;
//  end else begin
//    valid_r[0] <= valid_in[0];
//    valid_r[1] <= valid_in[1];
//    valid_r[2] <= valid_in[2];
//    valid_r[3] <= valid_in[3];
//  end
//end

//// Logic to assign valid_in for stages 1 to 3
//assign valid_in[1] = valid_r[0];
//assign valid_in[2] = valid_r[1];
//assign valid_in[3] = valid_r[2];
  
  always_ff @(posedge clk) begin
    if (rst)
      cntr_r <= 'b0;
    else if (pixel_en || cntr_r != 0)
      if (cntr_r == pKERNEL_SIZE*pKERNEL_SIZE)
        cntr_r <= 'b0;
      else //if (!buffer_valid)
        cntr_r <= cntr_r + 1'b1;    
  end
  
  always_ff @(posedge clk) begin
    if (rst)
      pixel_en <= 'b0;
    else
      pixel_en <= en;
  end
  
  always_ff @(posedge clk) begin
    if (rst)
      out_channel <= 'b0;
    else if (cntr_r == pKERNEL_SIZE*pKERNEL_SIZE)
      if (out_channel == pOUT_CHANNEL/pOUTPUT_PARALLEL-1)
        out_channel <= 'b0;
      else
        out_channel <= out_channel + 1'b1;
  end

  always_ff @(posedge clk) begin
    if (rst)
      pixel <= 'b0;
    else if (pixel == pKERNEL_SIZE*pKERNEL_SIZE-1)
      pixel <= 'b0;
    else if (cntr_r == pKERNEL_SIZE*pKERNEL_SIZE)// || buffer_valid
      pixel <= pixel;
    else if (pixel_en)   
      pixel <= pixel + 1'b1;
  end
  
  always_ff @(posedge clk) begin
    if (rst)
      kernel_addr <= 'b0;
    else if (pixel_en)
      if (kernel_addr == pKERNEL_NUM-1)
        kernel_addr <= 'b0;
      else if (cntr_r == pKERNEL_SIZE*pKERNEL_SIZE) // || buffer_valid
        kernel_addr <= kernel_addr;
      else
        kernel_addr <= kernel_addr + 1'b1;
  end
  
  always_ff @(posedge clk) begin
    if (rst)
      bias_addr <= 'b0;
    else if (bias_en)
      if (bias_addr == pBIAS_NUM-1)
        bias_addr <= 'b0;
      else   
        bias_addr <= bias_addr + 1'b1;
  end
  
  always_ff @(posedge clk) begin
    if (rst)
      buffer_idx <= 'b0;
    else if (valid_r[pVALID_STAGE_NUM-1])
      if (buffer_idx == pOUT_CHANNEL/pOUTPUT_PARALLEL-1)
        buffer_idx <= 'b0;
      else
        buffer_idx <= buffer_idx + 'b1;
  end
  
  assign pe_busy = ((pixel != 0 && (pixel != pKERNEL_SIZE*pKERNEL_SIZE-1 || out_channel != pOUT_CHANNEL/pOUTPUT_PARALLEL-1)) || pixel == 'b0) && en;
  assign pe_ready = !pe_busy;
  
  assign datapath_buffer_en = pixel == 'b0 && cntr_r == 'b0;
  
  assign clr_weight         = valid_r[1];
  assign adder_en_weight    = valid_r[1];
  assign mul_en             = valid_r[1 + pADDER_PIPE_STAGE_NUM];
  assign pe_clr             = valid_r[pADDER_STAGE_NUM-1];
  assign adder_en           = valid_r[pADDER_STAGE_NUM-1];
  assign sub_en             = valid_r[pSUB_STAGE_NUM-1];
  assign dequant_en         = valid_r[pDEQUAN_STAGE_NUM-1];
  assign bias_en            = valid_r[pBIAS_STAGE_NUM-1];
  assign act_en             = valid_r[pACT_STAGE_NUM-1];
  assign quant_en           = valid_r[pQUANT_STAGE_NUM-1];
  assign buffer_en          = valid_r[pBUFFER_STAGE_NUM-1];
  assign valid              = valid_r[pVALID_STAGE_NUM-1] && buffer_idx == pOUT_CHANNEL/pOUTPUT_PARALLEL-1;
  
  assign done = (count_valid == pOUT_WIDTH * pOUT_HEIGHT * (pOUT_CHANNEL/pOUTPUT_PARALLEL));
  
  always @(posedge clk) begin 
    if(rst)
        count_valid <= 0 ;
    else if(valid)
        count_valid <= count_valid + 1'b1;
    else if(count_valid >= pOUT_WIDTH * pOUT_HEIGHT * (pOUT_CHANNEL/pOUTPUT_PARALLEL))
        count_valid <= 0 ;
  end
  
endmodule