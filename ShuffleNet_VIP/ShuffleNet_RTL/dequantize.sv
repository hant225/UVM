`timescale 1ns/1ps

//(* use_dsp = "yes" *)
module dequantize (
   input  logic                 clk
  ,input  logic                 en
  ,input  logic                 rst
  ,input  logic signed  [31:0]  data_in
  ,input  logic signed  [31:0]  scale
  ,output logic signed  [31:0]  data_out
);

  logic [31:0] mult_out;
  logic signed  [31:0]  data_in_reg;
  logic signed  [31:0]  scale_reg;  
  
  always_ff @(posedge clk) begin
    if (rst) begin
      data_in_reg <= 'b0;
      scale_reg <= 'b0;
    end
    else if (en) begin
      data_in_reg <= data_in;
      scale_reg <= scale;
    end
  end
  
  assign data_out = mult_out;
  
  // pipeline stages: 8 , output MSB: 47, output LSB: 16,.
  mult_gen_1 mult_inst (
  .CLK(clk),  // input wire CLK
  .A(data_in_reg),      // input signed wire [31 : 0] A
  .B(scale_reg),      // input signed wire [31 : 0] B
  .P(mult_out)      // output wire [31 : 0] P
);
endmodule

