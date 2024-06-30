`timescale 1ns/1ps

module dequant_ram #(
   parameter  pWEIGHT_DATA_WIDTH  = 64
  ,parameter  pWEIGHT_BASE_ADDR   = 32'h4000_0000
  
  ,parameter  pDEQUANT_SCALE_NUM  = 32
  ,parameter  pBLOCK_RAM_NUM      = 32
)(
   input  logic                                         clk
  ,input  logic                                         rst
  ,input  logic                                         wr_en
  ,input  logic [31:0]                                  weight_addr
  ,input  logic [pWEIGHT_DATA_WIDTH-1:0]                weight_data
  ,output logic [pWEIGHT_DATA_WIDTH*pBLOCK_RAM_NUM*pDEQUANT_SCALE_NUM-1:0] dequant_scale_data
);
  
  (* ram_style = "block" *)
  logic  [pBLOCK_RAM_NUM-1:0][pDEQUANT_SCALE_NUM-1:0][pWEIGHT_DATA_WIDTH-1:0] dequant_scale_r;
  logic [$clog2(pBLOCK_RAM_NUM)-1:0] ram_idx;
  logic cs;
  
  assign cs = (weight_addr >= pWEIGHT_BASE_ADDR) && (weight_addr < pWEIGHT_BASE_ADDR + pDEQUANT_SCALE_NUM);
    
  always_ff @(posedge clk) begin
    if (rst || ram_idx == pBLOCK_RAM_NUM-1)
      ram_idx <= 'b0;
    else if (wr_en && cs)
      ram_idx <= ram_idx + 1'b1;
  end
  
  genvar idx;

  generate
    for (idx = 0; idx < pBLOCK_RAM_NUM; idx = idx+1) begin
      always_ff @(posedge clk) begin
        if (cs && wr_en && idx == ram_idx)
          dequant_scale_r[idx][weight_addr - pWEIGHT_BASE_ADDR] <= weight_data;
      end
    end
  endgenerate

  assign dequant_scale_data = dequant_scale_r;
endmodule