`timescale 1ns / 1ps


module SVA_pe_conv_mac_controller_conv1 #(   
     parameter  pOUT_CHANNEL      = 32    
    ,parameter  pKERNEL_SIZE      = 3       
    ,parameter  pOUTPUT_PARALLEL  = 32        
    ,parameter  pKERNEL_NUM       = 9  
    ,parameter  pBIAS_NUM         = 16    
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
    ,output logic                                             datapath_buffer_en
    ,output logic                                             adder_en
    ,output logic                                             dequant_en
    ,output logic                                             bias_en
    ,output logic                                             act_en
    ,output logic                                             quant_en
    ,output logic                                             buffer_en
    ,output logic                                             valid
    ,output logic                                             done
);    
          
    sequence s_buffer_valid;
        @(posedge clk) $rose(buffer_valid) ##1 $fell(buffer_valid);
    endsequence      
    
    A_valid:      assert property (@(posedge clk) $rose(buffer_valid) |-> $rose(valid) ##1 ($fell(valid) and $fell(buffer_valid)))
                    $info("@%0t A_valid success", $time);
    A_adder_en:   assert property (@(posedge clk) s_buffer_valid |-> ##4 $rose(adder_en) ##1 $fell(adder_en))
                    $info("@%0t A_adder_en success", $time);                      
    A_bias_en:    assert property (@(posedge clk) s_buffer_valid |-> ##3 $rose(bias_en) ##1 $fell(bias_en))
                    $info("@%0t A_bias_en success", $time);          
    A_act_en:     assert property (@(posedge clk) s_buffer_valid |-> ##4 $rose(act_en) ##1 $fell(act_en))
                    $info("@%0t A_act_en success", $time);                                      
    A_dequant_en: assert property (@(posedge clk) s_buffer_valid |-> ##5 $rose(dequant_en) ##1 $fell(dequant_en))
                    $info("@%0t A_dequant_en success", $time);    
    A_quant_en:   assert property (@(posedge clk) s_buffer_valid |-> ##8 $rose(quant_en) ##1 $fell(quant_en))
                    $info("@%0t A_quant_en success", $time); 
    A_buffer_en:  assert property (@(posedge clk) s_buffer_valid |-> ##9 $rose(buffer_en) ##1 $fell(buffer_en))
                    $info("@%0t A_buffer_en success", $time);       
                                                                           
endmodule
