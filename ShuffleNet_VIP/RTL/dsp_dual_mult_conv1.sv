`timescale 1ns/1ps

module dsp_dual_mult_conv1 (
   input  logic                 clk
  ,input  logic                 rst
  ,input  logic                 en
  ,input  logic signed  [7:0]   a
  ,input  logic signed  [7:0]   b
  ,input  logic         [7:0]   c
  ,output logic signed  [15:0]  ac
  ,output logic signed  [15:0]  bc
  ,output logic                 valid_out
);


  logic signed [25:0] dsp_a_pipe;
  logic signed [26:0] dsp_d_pipe;
  logic signed [17:0] dsp_b_pipe_0;
  
  logic signed [26:0] dsp_ad_pipe;
  logic signed [17:0] dsp_b_pipe_1;
  
  logic signed [33:0] dsp_mult_pipe;
  
  logic signed [33:0] dsp_p_pipe;
  
  logic signed  [7:0]   a_ext;
  logic signed  [7:0]   b_ext;
  logic         [7:0]   c_ext;
  
  logic [5:0] valid_r;

//  logic en_temp;
//  logic signed [7:0]a_temp,b_temp;
//  logic [7:0] c_temp;
  

  
//  always @(posedge  clk) begin
//    if(rst)
//        en_temp <= 1'b0;
//    else
//        en_temp <= en;
//  end
  
//  always @(posedge  clk) begin
//    if(rst)begin
//        a_temp <= 8'b0;
//        b_temp <= 8'b0;
//        c_temp <= 8'b0;
//    end        
//    else begin
//        a_temp <= a;
//        b_temp <= b;
//        c_temp <= c;    
//    end 
//  end
   
  always_ff @(posedge clk) begin
    if(rst) begin
        valid_r[0] <= 'b0;
        valid_r[1] <= 'b0;
        valid_r[2] <= 'b0;
        valid_r[3] <= 'b0;
        valid_r[4] <= 'b0;    
        valid_r[5] <= 'b0;    
          
    end
    else begin
        valid_r[0] <= en;    
        valid_r[1] <= valid_r[0];  
        valid_r[2] <= valid_r[1]; 
        valid_r[3] <= valid_r[2]; 
        valid_r[4] <= valid_r[3];                                 
        valid_r[5] <= valid_r[4];                                 
    end                          
  end
////  genvar idx;
////  generate
////    for (idx = 0; idx < 5; idx = idx+1) begin
////      logic valid_in;
      
////      if (idx)
////        assign valid_in = valid_r[idx-1];
////      else
////        assign valid_in = en;
        
////      always_ff @(posedge clk) begin
////        if (rst)
////          valid_r[idx] <= 'b0;
////        else
////          valid_r[idx] <= valid_in;
////      end
////    end
////  endgenerate

  always_ff @(posedge clk) begin
    if (rst) begin
      a_ext <= 'b0;
      b_ext <= 'b0;
      c_ext <= 'b0;
    end
    else begin
      a_ext <= a;
      b_ext <= b;
      c_ext <= c;
    end
  end
    
  // stage 1
  always_ff @(posedge clk) begin
    if (rst) begin
      dsp_a_pipe <= 'b0;
      dsp_d_pipe <= 'b0;
      dsp_b_pipe_0 <= 'b0;
    end
    else if (valid_r[0]) begin
      dsp_a_pipe <= {a_ext, 18'b0};
      dsp_d_pipe <= {{19{b[7]}}, b_ext};
      dsp_b_pipe_0 <= {10'b0, c_ext};
    end
  end
  
  //stage 2
  always_ff @(posedge clk) begin
    if (rst) begin
      dsp_ad_pipe <= 'b0;
      dsp_b_pipe_1 <= 'b0;
    end
    else if (valid_r[1]) begin
      dsp_ad_pipe <= dsp_a_pipe + dsp_d_pipe;
      dsp_b_pipe_1 <= dsp_b_pipe_0;
    end
  end
   
  // stage 3
  always_ff @(posedge clk) begin
    if (rst)
      dsp_mult_pipe <= 'b0;
    else if (valid_r[2]) begin
      dsp_mult_pipe <= dsp_ad_pipe * dsp_b_pipe_1;
    end
  end  
  
  // stage 4
  always_ff @(posedge clk) begin
    if (rst)
      dsp_p_pipe <= 'b0;
    else if (valid_r[3]) begin
      dsp_p_pipe <= dsp_mult_pipe;
    end
  end
  

  // stage 5
  always_ff @(posedge clk) begin
    if (rst) begin
      ac <= 'b0;
      bc <= 'b0;
    end
    else if (valid_r[4]) begin
      ac <= dsp_p_pipe[33:18] + dsp_p_pipe[15];
      bc <= dsp_p_pipe[15:0];
    end
  end
  
  assign valid_out = valid_r[5];

endmodule