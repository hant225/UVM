`timescale 1ns / 1ps
//////////////////////////////////////////////////////////////////////////////////
// Company: 
// Engineer: 
// 
// Create Date: 03/29/2024 12:23:02 PM
// Design Name: 
// Module Name: test_scb_result_queue
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

typedef logic[255:0] assoc_result     [string];
typedef int          int_assoc_result [string];

module test_scb_result_queue;
    // logic
    assoc_result result_queue[$];   // queue of assoc array
    assoc_result current_trans;
    // int
    int_assoc_result int_result_queue[$];
    int_assoc_result int_current_trans;
    
    
    logic         rst;
    logic         en;
    logic         buffer_in_en;
    logic [71:0]  data_in;
    logic         load_weight;
    logic [31:0]  weight_addr;
    logic [63:0]  weight_data;
    logic [255:0] data_out;
    logic         valid;
    logic         done;
    logic         pe_ready;
    
    int irst;
    int ien;
    int ibuffer_in_en;
    int idata_in;
    int iload_weight;
    int iweight_addr;
    int iweight_data;
    int idata_out;
    int ivalid;
    int idone;
    int ipe_ready;
    
    initial begin
        repeat(3) begin
            rst          = $urandom();
            en           = $urandom();
            buffer_in_en = $urandom();
            data_in      = $urandom();
            load_weight  = $urandom();
            weight_addr  = $urandom();
            weight_data  = $urandom();
            data_out     = $urandom();
            valid        = $urandom();
            done         = $urandom();
            pe_ready     = $urandom();
            
            irst          = rst         ;
            ien           = en          ;
            ibuffer_in_en = buffer_in_en;
            idata_in      = data_in     ;
            iload_weight  = load_weight ;
            iweight_addr  = weight_addr ;
            iweight_data  = weight_data ;
            idata_out     = data_out    ;
            ivalid        = valid       ;
            idone         = done        ;
            ipe_ready     = pe_ready    ;
              
            current_trans["rst"]          = rst         ;
            current_trans["en"]           = en          ;
            current_trans["buffer_in_en"] = buffer_in_en;
            current_trans["data_in"]      = data_in     ;
            current_trans["load_weight"]  = load_weight ;
            current_trans["weight_addr"]  = weight_addr ;
            current_trans["weight_data"]  = weight_data ;
            current_trans["data_out"]     = data_out    ;
            current_trans["valid"]        = valid       ;
            current_trans["done"]         = done        ;
            current_trans["pe_ready"]     = pe_ready    ;
            
            int_current_trans["rst"]          = irst         ;
            int_current_trans["en"]           = ien          ;
            int_current_trans["buffer_in_en"] = ibuffer_in_en;
            int_current_trans["data_in"]      = idata_in     ;
            int_current_trans["load_weight"]  = iload_weight ;
            int_current_trans["weight_addr"]  = iweight_addr ;
            int_current_trans["weight_data"]  = iweight_data ;
            int_current_trans["data_out"]     = idata_out    ;
            int_current_trans["valid"]        = ivalid       ;
            int_current_trans["done"]         = idone        ;
            int_current_trans["pe_ready"]     = ipe_ready    ;
            
            result_queue.push_back(current_trans);
            int_result_queue.push_back(int_current_trans);
        end
        
        foreach(result_queue[i])
            foreach(result_queue[i][key]) 
                $display("[%0d] key : %-15s - value : %0d", i, key, $signed(result_queue[i][key]));
        
        $display();
        foreach(int_result_queue[i])
            foreach(int_result_queue[i][key]) 
                $display("[%0d] key : %-15s - value : %0d", i, key, int_result_queue[i][key]);
    end
endmodule
