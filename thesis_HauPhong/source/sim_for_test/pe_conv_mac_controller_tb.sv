`timescale 1ns / 1ps
//////////////////////////////////////////////////////////////////////////////////
// Company: 
// Engineer: 
// 
// Create Date: 03/28/2024 09:20:16 PM
// Design Name: 
// Module Name: pe_conv_mac_controller_tb
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


module pe_conv_mac_controller_tb;
   logic        clk;               
   logic        rst;               
   logic        en;                
   logic        buffer_valid;      
   logic [8:0]  pixel;             
   logic [9:0]  kernel_addr;       
   logic [5:0]  bias_addr;         
   logic [-1:0] buffer_idx;        
   logic        pe_ready;          
   logic        pe_clr;            
   logic        datapath_buffer_en;
   logic        adder_en;          
   logic        dequant_en;        
   logic        bias_en;           
   logic        act_en;            
   logic        quant_en;          
   logic        buffer_en;         
   logic        valid;             
   logic        done;              

    pe_conv_mac_controller_conv1 #(   
        .pIN_CHANNEL     ( 1    ),
        .pOUT_CHANNEL    ( 32   ),
        .pKERNEL_SIZE    ( 3    ),
        .pOUTPUT_PARALLEL( 32   ),
        .pKERNEL_NUM     ( 1024 ),
        .pBIAS_NUM       ( 32   ),                        
        .pINPUT_WIDTH    ( 28   ),
        .pINPUT_HEIGHT   ( 28   ),
        .pPADDING        ( 1    ),
        .pSTRIDE         ( 1    ),
        .pACTIVATION     ("sigmoid")
    ) DUT (
        .clk(clk),
        .rst(rst),
        .en(en),
        .buffer_valid(buffer_valid),
        .pixel(pixel),
        .kernel_addr(kernel_addr),
        .bias_addr(bias_addr),
        .buffer_idx(buffer_idx),
        .pe_ready(pe_ready),
        .pe_clr(pe_clr),
        .datapath_buffer_en(datapath_buffer_en),
        .adder_en(adder_en),
        .dequant_en(dequant_en),
        .bias_en(bias_en),
        .act_en(act_en),
        .quant_en(quant_en),
        .buffer_en(buffer_en),
        .valid(valid),
        .done(done)
    );
    
    initial begin
        clk = 0; rst = 0; en = 0; buffer_valid = 0;
        #195  rst = 1;
        #20   rst = 0; 
        #40   en = 1;
        #650  for(int i = 0; i < 5; i++) begin
                   #20000 buffer_valid = 1; 
                   #200    buffer_valid = 0; 
               end  
        
        $finish;
    end
    
    always #10 clk = ~clk;
endmodule
