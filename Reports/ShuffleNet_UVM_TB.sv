`timescale 1ns / 1ps
`include "uvm_macros.svh"
import uvm_pkg::*; 
//////////////////////////////////////////////////////////////////////////////////
// Company: 
// Engineer: 
// 
// Create Date: 07/15/2024 01:49:47 PM
// Design Name: 
// Module Name: ShuffleNet_top_tb
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
   
//////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
// PACKAGES //////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
typedef enum bit[3:0] {RESET, 
                           MEM_KERNEL_LOAD, 
                           MEM_BIAS_LOAD, 
                           MEM_DEQUANT_SCALE_LOAD,
                           MEM_QUANT_SCALE_LOAD, 
                           LOAD_PIXELS,
                           PE_RUNNING} oper_mode;

package shared_pkg;
    localparam pDATA_WIDTH        = 8;    
    localparam pWEIGHT_DATA_WIDTH = 64;
    localparam pWEIGHT_BASE_ADDR  = 32'h4000_0000;        
endpackage

package conv1_pkg;
    import shared_pkg::*;
    
    localparam pINPUT_WIDTH       = 224;
    localparam pINPUT_HEIGHT      = 224;          
    localparam pIN_CHANNEL        = 3;
    localparam pOUT_CHANNEL       = 24;    
    localparam pKERNEL_SIZE       = 3;
    localparam pPADDING           = 1;
    localparam pSTRIDE            = 2;    
    localparam pACTIVATION        = "relu";
    localparam pOUTPUT_PARALLEL   = 24;
        
    localparam pOUTPUT_WIDTH      = (pINPUT_WIDTH - pKERNEL_SIZE + 2*pPADDING)/pSTRIDE + 1;
    localparam pOUTPUT_HEIGHT     = (pINPUT_HEIGHT - pKERNEL_SIZE + 2*pPADDING)/pSTRIDE + 1;    
    localparam pRATIO             = pOUT_CHANNEL/pOUTPUT_PARALLEL;    
    localparam pULTRA_RAM_NUM     = (pIN_CHANNEL*pOUTPUT_PARALLEL)/8;
    localparam pBLOCK_RAM_NUM     = pOUTPUT_PARALLEL/2;    
    localparam pKERNEL_NUM        = pIN_CHANNEL*pOUT_CHANNEL*pKERNEL_SIZE*pKERNEL_SIZE / (pWEIGHT_DATA_WIDTH/pDATA_WIDTH);
    localparam pBIAS_NUM          = pOUT_CHANNEL / 2;
    localparam pDEQUANT_SCALE_NUM = pOUT_CHANNEL;    
    localparam pWEIGHTS_NUM       = pKERNEL_NUM + pBIAS_NUM + pDEQUANT_SCALE_NUM+ 1;
    localparam weight_path        = "/home/hao/Documents/0.KHOA_LUAN_TOT_NGHIEP/shuffle_net/HauPhong_Weight/weights/conv1/total_weights.txt"; 
    localparam image_path         = "/home/hao/Documents/0.KHOA_LUAN_TOT_NGHIEP/shuffle_net/ShuffleNet_VIP/InputData/conv1/pixel_image.txt";
    localparam img_data_path      = "/home/hao/Documents/0.KHOA_LUAN_TOT_NGHIEP/shuffle_net/ShuffleNet_Evaluation/conv1_output/img_data_in.txt";
    localparam result_path        = "/home/hao/Documents/0.KHOA_LUAN_TOT_NGHIEP/shuffle_net/ShuffleNet_Evaluation/conv1_output/real_results/";
endpackage

package convDW_pkg;                        
    localparam pINPUT_WIDTH       = 56;
    localparam pINPUT_HEIGHT      = 56;               
    localparam pIN_CHANNEL        = 24;
    localparam pOUT_CHANNEL       = 24;    
    localparam pKERNEL_SIZE       = 3;
    localparam pPADDING           = 1;
    localparam pSTRIDE            = 2;    
    localparam pACTIVATION        = "";
    localparam pOUTPUT_PARALLEL   = 24;   
    localparam pZERO_POINT_NUM    = 1;      
    
    localparam pOUTPUT_WIDTH      = (pINPUT_WIDTH - pKERNEL_SIZE + 2*pPADDING)/pSTRIDE + 1;
    localparam pOUTPUT_HEIGHT     = (pINPUT_HEIGHT - pKERNEL_SIZE + 2*pPADDING)/pSTRIDE + 1;    
    localparam pRATIO             = pOUT_CHANNEL/pOUTPUT_PARALLEL;    
    localparam pULTRA_RAM_NUM     = int'($ceil(real'(pOUT_CHANNEL)/real'(8)));
    localparam pBLOCK_RAM_NUM     = pOUT_CHANNEL/2;    
    localparam pKERNEL_NUM        = 9*pULTRA_RAM_NUM;
    localparam pBIAS_NUM          = 1*pBLOCK_RAM_NUM;
    localparam pDEQUANT_SCALE_NUM = pOUT_CHANNEL;       
    localparam pWEIGHTS_NUM       = pKERNEL_NUM + pBIAS_NUM + pDEQUANT_SCALE_NUM + pZERO_POINT_NUM + 1;    
    localparam weight_path        = "/home/hao/Documents/0.KHOA_LUAN_TOT_NGHIEP/shuffle_net/HauPhong_Weight/weights/convDW_stage2_0_branch1_0_fp/export_total_weight.txt";                                                                                                                                                                     
    localparam image_path         = "/home/hao/Documents/0.KHOA_LUAN_TOT_NGHIEP/shuffle_net/ShuffleNet_VIP/InputData/convDW/pixel_image.txt";                                    
    localparam img_data_path      = "/home/hao/Documents/0.KHOA_LUAN_TOT_NGHIEP/shuffle_net/ShuffleNet_Evaluation/convDW_output/img_data_in.txt";
    localparam result_path        = "/home/hao/Documents/0.KHOA_LUAN_TOT_NGHIEP/shuffle_net/ShuffleNet_Evaluation/convDW_output/real_results/";  
endpackage

//////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
// INTERFACE /////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////

interface conv1_if();
    oper_mode op;   
    logic                                                       clk;
    logic                                                       rst;
    logic                                                       en;        
    logic                                                       load_weight;
    logic [31:0]                                                weight_addr;
    logic [shared_pkg::pWEIGHT_DATA_WIDTH-1:0]                  weight_data;
    logic [shared_pkg::pDATA_WIDTH*conv1_pkg::pIN_CHANNEL-1:0]  data_in;
    logic [shared_pkg::pDATA_WIDTH*conv1_pkg::pOUT_CHANNEL-1:0] data_out;
    logic                                                       valid;
    logic                                                       done;
endinterface

interface convDW_if();
    oper_mode op;
    logic                                                        clk;
    logic                                                        rst;
    logic                                                        en;        
    logic                                                        load_weight;
    logic [31:0]                                                 weight_addr;
    logic [shared_pkg::pWEIGHT_DATA_WIDTH-1:0]                   weight_data;
    logic [shared_pkg::pDATA_WIDTH*convDW_pkg::pIN_CHANNEL-1:0]  data_in;
    logic [shared_pkg::pDATA_WIDTH*convDW_pkg::pOUT_CHANNEL-1:0] data_out;
    logic                                                        valid;
    logic                                                        done;
endinterface

//////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
// DPI ///////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////

import "DPI-C" function void gen_conv1_input_and_rslt();
import "DPI-C" function void conv1_golden_model();
import "DPI-C" function void gen_convDW_input_and_rslt();
import "DPI-C" function void convDW_golden_model();

//////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
// CONV1_TRANSACTION//////////////////////////////////////////////////////////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////

class conv1_transaction #(parameter pWEIGHT_DATA_WIDTH = shared_pkg::pWEIGHT_DATA_WIDTH,
                          parameter pDATA_WIDTH        = shared_pkg::pDATA_WIDTH,
                          parameter pIN_CHANNEL        = conv1_pkg::pIN_CHANNEL,
                          parameter pOUT_CHANNEL       = conv1_pkg::pOUT_CHANNEL) extends uvm_sequence_item;

    // Properties
    oper_mode op;
    logic                                rst;
    logic                                en;        
    logic                                load_weight;
    logic [31:0]                         weight_addr;
    logic [pWEIGHT_DATA_WIDTH-1:0]       weight_data;
    logic [pDATA_WIDTH*pIN_CHANNEL-1:0]  data_in;
    logic [pDATA_WIDTH*pOUT_CHANNEL-1:0] data_out;
    logic                                valid;
    logic                                done;                  
    
    // Constructor
    function new(input string path = "conv1_transaction");
        super.new(path);
    endfunction
    
    // Field Macros
    `uvm_object_utils_begin(conv1_transaction)
        `uvm_field_enum(oper_mode, op, UVM_DEFAULT)
        `uvm_field_int (rst,           UVM_DEFAULT)
        `uvm_field_int (en,            UVM_DEFAULT)               
        `uvm_field_int (load_weight,   UVM_DEFAULT)
        `uvm_field_int (weight_addr,   UVM_DEFAULT)
        `uvm_field_int (weight_data,   UVM_DEFAULT)
        `uvm_field_int (data_in,       UVM_DEFAULT)
        `uvm_field_int (data_out,      UVM_DEFAULT)
        `uvm_field_int (valid,         UVM_DEFAULT)
        `uvm_field_int (done,          UVM_DEFAULT)       
    `uvm_object_utils_end
    
    // Display Method
    function void tr_display(string class_name);
        if(class_name != "DRV" && class_name != "MON" && class_name != "SCB")
            `uvm_error("SEQ_ITEM", $sformatf("%0s IS AN ILLEGAL CLASS NAME", class_name))
            
        `uvm_info(class_name, "--------------------------------------Transaction Info--------------------------------------", UVM_NONE)
        `uvm_info(class_name, $sformatf("op           = %s",  this.op.name), UVM_NONE)
        `uvm_info(class_name, $sformatf("en           = %0b", this.en), UVM_NONE)              
        `uvm_info(class_name, $sformatf("load_weight  = %0b", this.load_weight), UVM_NONE)
        `uvm_info(class_name, $sformatf("weight_addr  = %0h - dunkare", this.weight_addr), UVM_NONE)
        `uvm_info(class_name, $sformatf("weight_data  = %0h - dunkare", this.weight_data), UVM_NONE)
        `uvm_info(class_name, $sformatf("data_in      = %0h", this.data_in), UVM_NONE)
        if(class_name == "MON" || class_name == "SCB") begin
            `uvm_info(class_name, $sformatf("data_out     = %0h", this.data_out), UVM_NONE)
            `uvm_info(class_name, $sformatf("valid        = %0b", this.valid), UVM_NONE)
            `uvm_info(class_name, $sformatf("done         = %0b", this.done), UVM_NONE)                        
        end
        `uvm_info(class_name, "--------------------------------------------------------------------------------------------", UVM_NONE)
    endfunction
endclass : conv1_transaction

//////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
// CONV1_SEQUENCE ////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////

class conv1_std_seq #(parameter pDATA_WIDTH        = shared_pkg::pDATA_WIDTH,
                      parameter pWEIGHT_DATA_WIDTH = shared_pkg::pWEIGHT_DATA_WIDTH,
                      parameter pWEIGHT_BASE_ADDR  = shared_pkg::pWEIGHT_BASE_ADDR,
                      parameter pIN_CHANNEL        = conv1_pkg::pIN_CHANNEL,
                      parameter pOUT_CHANNEL       = conv1_pkg::pOUT_CHANNEL,
                      parameter pINPUT_WIDTH       = conv1_pkg::pINPUT_WIDTH,
                      parameter pINPUT_HEIGHT      = conv1_pkg::pINPUT_HEIGHT,
                      parameter pULTRA_RAM_NUM     = conv1_pkg::pULTRA_RAM_NUM,
                      parameter pBLOCK_RAM_NUM     = conv1_pkg::pBLOCK_RAM_NUM,
                      parameter pKERNEL_NUM        = conv1_pkg::pKERNEL_NUM,
                      parameter pBIAS_NUM          = conv1_pkg::pBIAS_NUM,
                      parameter pDEQUANT_SCALE_NUM = conv1_pkg::pDEQUANT_SCALE_NUM,
                      parameter pWEIGHTS_NUM       = conv1_pkg::pWEIGHTS_NUM,
                      parameter weight_path        = conv1_pkg::weight_path, 
                      parameter image_path         = conv1_pkg::image_path,
                      parameter pZEROPOINT_LOAD    = 1,
                      type      T_TRANS            = conv1_transaction                            
                     ) extends uvm_sequence#(T_TRANS);       
    
    // Register to Factory
    `uvm_object_utils(conv1_std_seq)        
        
    // Properties   
    T_TRANS tr;    
    int ram_idx = 0;
    int scale   = 0; 
    int addr    = 0;  
    int fd      = 0;        
    int trans_amount = pINPUT_WIDTH * pINPUT_HEIGHT;    
    
    logic [pDATA_WIDTH*pIN_CHANNEL-1:0] in_fm   [0:pINPUT_WIDTH*pINPUT_HEIGHT-1];
    logic [pWEIGHT_DATA_WIDTH-1:0]      weights [0:pWEIGHTS_NUM-1];                
    
    // Constructor
    function new(input string path = "std_seq");
        super.new(path);
    endfunction
    
    // Body
    virtual task body();
        set_response_queue_error_report_disabled(1);
        tr = T_TRANS::type_id::create("tr");
        do_load_weight(tr);        
        create_data_seq(tr);  
        running_state(tr);             
    endtask
    
    // Weight Load Method
    virtual task do_load_weight(T_TRANS tr);                  
            // Common Signals for loading weights
            tr.rst         = 1'b0;
            tr.en          = 1'b0;
            tr.load_weight = 1'b1;            
                                 
            // Read weights from file here
            fd = $fopen(weight_path, "r");
            if(!fd) `uvm_fatal("SEQ", "Unable to read Weights File");
            $readmemh(weight_path, weights);
            $fclose(fd);                            
                                    
            // 1. Kerrnel weights -----------------------------------------------------------------------------------------------------                     
            for(int i = 0; i < pKERNEL_NUM; i = i + 1) begin
                start_item(tr);                    
                    tr.op          = MEM_KERNEL_LOAD;                      
                    tr.weight_addr = i - ram_idx - (pULTRA_RAM_NUM-1)*scale + pWEIGHT_BASE_ADDR;
                    tr.weight_data = weights[addr++];    
                    `uvm_info("SEQ_DEBUG", "Before finish_item(tr)", UVM_NONE)     
                    `uvm_info("SEQ_DEBUG", $sformatf("[%s] Weight Loaded: weight_addr = %0h , weight_data = %16h", tr.op.name, tr.weight_addr, tr.weight_data), UVM_NONE)           
                finish_item(tr);
                `uvm_info("SEQ_DEBUG", "After finish_item(tr)", UVM_NONE)
                 
                if (ram_idx == pULTRA_RAM_NUM-1) begin
                    ram_idx = 0;
                    scale   = scale + 1;
                end else begin
                    ram_idx = ram_idx + 1;
                end
            end              
                                                           
            // 2. Bias weights --------------------------------------------------------------------------------------------------------
            ram_idx = 0;
            scale   = 0;
            for(int i = 0; i < pBIAS_NUM; i++) begin
                start_item(tr);                    
                    tr.op          = MEM_BIAS_LOAD;
                    tr.weight_addr = i - ram_idx - (pBLOCK_RAM_NUM-1)*scale + pWEIGHT_BASE_ADDR + pKERNEL_NUM/pULTRA_RAM_NUM;
                    tr.weight_data = weights[addr++]; 
                finish_item(tr);                                     

                if (ram_idx == pBLOCK_RAM_NUM-1) begin
                    ram_idx = 0;
                    scale   = scale + 1;
                end else begin
                    ram_idx = ram_idx + 1;
                end
            end
          
            // 3. Dequantize Scale weights --------------------------------------------------------------------------------------------            
            ram_idx = 0;
            scale   = 0;
            load_dequantize_scale_weights(ram_idx, scale);                        
            
            // 4. Quantize Scale weights ----------------------------------------------------------------------------------------------
            repeat(pZEROPOINT_LOAD) begin
                start_item(tr);                
                    tr.op          = MEM_QUANT_SCALE_LOAD;
                    tr.weight_addr = tr.weight_addr + 1;
                    tr.weight_data = weights[addr++];
                finish_item(tr);  
            end
            
            `uvm_info("STD_SEQ", "Memory Weights Load Finished. Start Generating Transaction Data!", UVM_NONE)
    endtask
    
    // Task for load dequantize weights because CONV1, CONV1x1, CONDW has same load kernel,
    // bias and scale weights method but has a small different in dequant scale weight load.
    // Split the load dequantize scale help overriding this method in child class in the future  
    virtual task load_dequantize_scale_weights(input int ram_idx, input int scale);
        for(int i = 0; i < pDEQUANT_SCALE_NUM; i++) begin
            start_item(tr);                    
                tr.op          = MEM_DEQUANT_SCALE_LOAD;
                tr.weight_addr = i - ram_idx - (pBLOCK_RAM_NUM-1)*scale + pWEIGHT_BASE_ADDR + pKERNEL_NUM/pULTRA_RAM_NUM + 1;
                tr.weight_data = weights[addr++];
            finish_item(tr);                                    
            
            if(ram_idx == pOUT_CHANNEL-1) begin
                ram_idx = 0;
                scale   = scale + 1;
            end else begin
                ram_idx = ram_idx + 1;
            end
        end
    endtask
    
    // Create Data Sequence Method
    virtual task create_data_seq(T_TRANS tr);                              
        gen_conv1_input_and_rslt();                           // Call C routine
        $readmemh(image_path, in_fm);                         // Read image to array                                           
        for(int i = 0; i < trans_amount; i++) begin           // Create seq items
            start_item(tr);
                tr.op           = LOAD_PIXELS;                            
                tr.rst          = 1'b0;                
                tr.load_weight  = 1'b0;                
                tr.en           = 1'b1;           
                tr.data_in      = in_fm[i];     
                `uvm_info("STD_SEQ", $sformatf("[No.%0d] Transaction Generated: data_in = %0h", i, tr.data_in), UVM_NONE)
            finish_item(tr);
        end
    endtask
    
    // Finish Loading Weight and Pixel, Wait for PE to Finish
    virtual task running_state(T_TRANS tr);
        start_item(tr);
            tr.op          = PE_RUNNING;
            tr.rst         = 1'b0;
            tr.en          = 1'b0;
            tr.load_weight = 1'b0;
            tr.weight_data =  'dx;
            tr.data_in     =  'dx;
        finish_item(tr);                
    endtask
    
endclass : conv1_std_seq

//////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
// CONV1_DRIVER //////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////

class conv1_driver#(type T_TRANS = conv1_transaction) extends uvm_driver #(conv1_transaction);
    // Register to Factory
    `uvm_component_utils(conv1_driver)
    
    // Properties       
    T_TRANS tr;
    virtual conv1_if vif;
    
    // Constructor
    function new(input string path = "DRV", uvm_component parent = null);
        super.new(path, parent);
    endfunction
    
    // Build Phase
    virtual function void build_phase(uvm_phase phase);
        super.build_phase(phase);
        tr = T_TRANS::type_id::create("tr");
        if(!uvm_config_db#(virtual conv1_if)::get(this, "", "vif", vif))
            `uvm_error("DRV", "UNABLE TO ACCESS THE INTERFACE!!!")
    endfunction
    
    // Run phase
    virtual task run_phase(uvm_phase phase);
        drive();
    endtask
    
    // Methods
    virtual task drive();
        reset_DUT();
        forever begin
            seq_item_port.get_next_item(tr);   
                    vif.op           <= tr.op;
                    vif.rst          <= tr.rst; 
                    vif.load_weight  <= tr.load_weight;                             
                if(tr.load_weight) begin
                    vif.weight_addr  <= tr.weight_addr; 
                    vif.weight_data  <= tr.weight_data;
                    vif.data_in      <= 'dx;
                    vif.en           <= 1'b0;                                        
                    @(posedge vif.clk);  
                    `uvm_info("DRV", $sformatf("[%s] Weight Loaded: weight_addr = %0h , weight_data = %16h", tr.op.name, tr.weight_addr, tr.weight_data), UVM_NONE)
                end 
                else if(!tr.load_weight) begin
                    vif.weight_addr  <= 'dx;
                    vif.weight_data  <= 'dx;
                    vif.en           <= tr.en;
                    vif.data_in      <= tr.data_in;
                    tr.tr_display("DRV");
                    @(posedge vif.clk);
                end
                `uvm_info("DRV_DEBUG", "Before item_done(tr)", UVM_NONE)
            seq_item_port.item_done(tr);
            `uvm_info("DRV_DEBUG", "After item_done(tr)", UVM_NONE)
        end
    endtask
    
    
    // DUT reset
    virtual task reset_DUT();
        repeat(5) begin 
            vif.op  <= RESET;
            vif.rst <= 1'b1;
            @(posedge vif.clk);
        end
        `uvm_info("DRV", "SYSTEM RESET: START OF SIMULATION", UVM_NONE)
    endtask
    
endclass : conv1_driver

//////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
// CONV1_MONITOR /////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////

class conv1_monitor#(type T_TRANS = conv1_transaction) extends uvm_monitor;
    // Register to Factory
    `uvm_component_utils(conv1_monitor)
    
    // Properties   
    T_TRANS tr;
    virtual conv1_if vif;  
    int valid_count = 0;  
    
    // Analysis Port
    uvm_analysis_port #(T_TRANS) send;
    
    // Constructor
    function new(input string path = "MON", uvm_component parent = null);
        super.new(path, parent);
    endfunction
    
    // Build Phase
    virtual function void build_phase(uvm_phase phase);
        super.build_phase(phase);
        tr = T_TRANS::type_id::create("tr");
        if(!uvm_config_db#(virtual conv1_if)::get(this, "", "vif", vif))
            `uvm_error("MON", "UNABLE TO ACCESS THE INTERFACE!!!");
        send = new("send", this);
    endfunction
    
    // Run phase
    virtual task run_phase(uvm_phase phase);
        phase.raise_objection(this);        
        forever begin
            @(posedge vif.clk);           
            tr.op = vif.op;         
            if(tr.op == RESET) begin
                tr.rst = 1'b1;
                `uvm_info("MON", "SYSTEM RESET DETECTED", UVM_NONE);
            end 
            else begin
                    tr.rst          = 1'b0;
                    tr.load_weight  = vif.load_weight;  
                    tr.en           = vif.en;                     
                if(vif.done)                                          
                    phase.drop_objection(this);                       // Stop Run Phase when DUT done                       
                else if(vif.load_weight) begin                        // weight load process
                    tr.weight_addr  = vif.weight_addr;
                    tr.weight_data  = vif.weight_data;
                    tr.data_in      = 'dx;
                    `uvm_info("MON", $sformatf("[%s] Weight Loaded: weight_addr = %0h , weight_data = %16h", tr.op.name, tr.weight_addr, tr.weight_data), UVM_NONE)
                end 
                else if(!vif.load_weight) begin                       // pe_conv_mac process                            
                    tr.data_in      = vif.data_in;
                    tr.data_out     = vif.data_out;
                    tr.valid        = vif.valid;                    
                    tr.done         = vif.done;                                        
                end                                                      
            end            
            // Send to Scoreboard
            send.write(tr);
            // Stop Run Phase
            if(tr.valid) begin
                valid_count = valid_count + 1;
                tr.tr_display("MON");
                `uvm_info("MON", $sformatf("No. Valid : %0d", valid_count), UVM_NONE)
            end                       
        end
    endtask: run_phase    
    
endclass : conv1_monitor

//////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
// CONV1_AGENT ///////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////

class conv1_agent#(type T_TRANS   = conv1_transaction,
                   type T_DRIVER  = conv1_driver,
                   type T_MONITOR = conv1_monitor) extends uvm_agent;
    // Register to Factory
    `uvm_component_utils(conv1_agent)
    
    // Properties
    T_DRIVER  d;
    T_MONITOR m;
    uvm_sequencer #(T_TRANS) seqr;    
    
    // Constructor
    function new(input string path = "AGENT", uvm_component parent = null);
        super.new(path, parent);       
    endfunction
    
    // Build Phase
    virtual function void build_phase(uvm_phase phase);
        super.build_phase(phase);
        d    = T_DRIVER::type_id::create("d", this);
        m    = T_MONITOR::type_id::create("m", this);
        seqr = uvm_sequencer#(T_TRANS)::type_id::create("seqr", this);
    endfunction
    
    // Connect Phase
    virtual function void connect_phase(uvm_phase phase);
        super.connect_phase(phase);
        d.seq_item_port.connect(seqr.seq_item_export);
    endfunction
endclass : conv1_agent

//////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
// CONV1_SCOREBOARD //////////////////////////////////////////////////////////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////

class conv1_scoreboard #(type      T_TRANS        = conv1_transaction,                         
                         parameter pDATA_WIDTH    = shared_pkg::pDATA_WIDTH,
                         parameter pINPUT_WIDTH   = conv1_pkg::pINPUT_WIDTH,
                         parameter pINPUT_HEIGHT  = conv1_pkg::pINPUT_HEIGHT,
                         parameter pIN_CHANNEL    = conv1_pkg::pIN_CHANNEL,
                         parameter pOUT_CHANNEL   = conv1_pkg::pOUT_CHANNEL,
                         parameter pKERNEL_SIZE   = conv1_pkg::pKERNEL_SIZE,
                         parameter pPADDING       = conv1_pkg::pPADDING,
                         parameter pSTRIDE        = conv1_pkg::pSTRIDE,
                         parameter pOUTPUT_WIDTH  = conv1_pkg::pOUTPUT_WIDTH,
                         parameter pOUTPUT_HEIGHT = conv1_pkg::pOUTPUT_HEIGHT,        
                         parameter img_data_path  = conv1_pkg::img_data_path,
                         parameter result_path    = conv1_pkg::result_path ) extends uvm_scoreboard;
    
    // Register to Factory
    `uvm_component_utils(conv1_scoreboard)     
    
    // Analysis Imp
    uvm_analysis_imp#(T_TRANS, this) recv;
    
    // Properties
    int addr = 0; 
    int fd = 0;         
    logic [pDATA_WIDTH*pIN_CHANNEL-1:0] arr_data_in [pINPUT_WIDTH*pINPUT_HEIGHT]; 
    logic [pDATA_WIDTH-1:0]             out_fm      [0:pOUT_CHANNEL-1][0:pOUTPUT_WIDTH*pOUTPUT_HEIGHT-1];
            
    // Constructor
    function new(input string path = "SCB", uvm_component parent = null);
        super.new(path, parent);        
    endfunction
    
    // Build Phase
    virtual function void build_phase(uvm_phase phase);
        super.build_phase(phase);
        recv = new("recv", this);                        
    endfunction
    
    // Extract Phase
    virtual function void extract_phase(uvm_phase phase);
        super.extract_phase(phase);                
        for (int i = 0; i < pOUT_CHANNEL; i = i + 1) begin
            $writememh($sformatf("%s/DUT_out_channel_%0d.txt", result_path, i), out_fm[i]);
        end                        
    endfunction
    
    // Check Phase
    virtual function void check_phase(uvm_phase phase);
        super.check_phase(phase);
        `uvm_info("SCB", "[CHECK PHASE] START CHECKING PROCESS\n", UVM_NONE)
        predictor();
    endfunction
    
    // Report Phase
    virtual function void report_phase(uvm_phase phase);
        super.report_phase(phase);
        `uvm_info("SCB", "[REPORT PHASE] START CHECKING PROCESS\n", UVM_NONE)
    endfunction
    
    // Write Method
    virtual function void write(T_TRANS tr);
        if(tr.op == RESET)             
            reset_state();
        else if (tr.op != LOAD_PIXELS && tr.op != PE_RUNNING)  
            `uvm_info("SCB", "LOADING WEIGHTS TO DUT..", UVM_NONE)
        else
            collect_data(tr);
    endfunction           
    
    // Reset State
    function reset_state();
        `uvm_info("SCB", "SYSTEM RESET..", UVM_NONE)
        fd = $fopen(img_data_path, "w");
        if(!fd) `uvm_fatal("SCB", "Unable to create image data file!")
        $fclose(fd);
    endfunction         
    
    // Collect Results
    virtual function collect_data(T_TRANS tr);    
        // Double check the input image
        if(tr.en) begin
            fd = $fopen(img_data_path, "a");
            if(!fd) `uvm_fatal("SCB", "Unable to open output image data file!")
            $fwrite(fd, "%2h%2h%2h\n", tr.data_in[23:16], tr.data_in[15:8], tr.data_in[7:0]);
            $fclose(fd);
        end
    
        // Collect data_out if tr.valid = 1'b1
        if(tr.valid) begin            
            for (int i = 0; i < pOUT_CHANNEL; i = i + 1) begin
                out_fm[i][addr] = tr.data_out[pDATA_WIDTH*i +: pDATA_WIDTH];
            end
            addr = addr + 1;
        end
    endfunction
    
    // Predictor
    function predictor();   
        `uvm_info("SCB", "Start checking result..", UVM_NONE);
        conv1_golden_model();                   
    endfunction
      
endclass : conv1_scoreboard

//////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
// CONV1_ENV /////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////

class conv1_env#(type T_SCOREBOARD = conv1_scoreboard,
                 type T_AGENT      = conv1_agent      ) extends uvm_env;

    // Register to Factory
    `uvm_component_utils(conv1_env)

    // Properties
    T_SCOREBOARD s;
    T_AGENT      a;
    
    // Constructor
    function new(input string path = "ENV", uvm_component parent = null);
        super.new(path, parent);       
    endfunction
    
    // Build Phase
    virtual function void build_phase(uvm_phase phase);
        super.build_phase(phase);
        s  = T_SCOREBOARD::type_id::create("s", this);
        a  = T_AGENT::type_id::create("a", this);        
    endfunction
    
    // Connect Phase
    virtual function void connect_phase(uvm_phase phase);
        super.connect_phase(phase);
        a.m.send.connect(s.recv);        
    endfunction

endclass : conv1_env

//////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
// CONVDW_TRANSACTION ////////////////////////////////////////////////////////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////

class convDW_transaction extends conv1_transaction #(.pWEIGHT_DATA_WIDTH (shared_pkg::pWEIGHT_DATA_WIDTH),
                                                     .pDATA_WIDTH        (shared_pkg::pDATA_WIDTH),
                                                     .pIN_CHANNEL        (convDW_pkg::pIN_CHANNEL),
                                                     .pOUT_CHANNEL       (convDW_pkg::pOUT_CHANNEL));        
    
    // Constructor
    function new(input string path = "convDW_transaction");
        super.new(path);
    endfunction    
        
    // Field Macros
    `uvm_object_utils_begin(convDW_transaction)        
        `uvm_field_enum(oper_mode, op, UVM_DEFAULT)
        `uvm_field_int (rst,           UVM_DEFAULT)
        `uvm_field_int (en,            UVM_DEFAULT)               
        `uvm_field_int (load_weight,   UVM_DEFAULT)
        `uvm_field_int (weight_addr,   UVM_DEFAULT)
        `uvm_field_int (weight_data,   UVM_DEFAULT)
        `uvm_field_int (data_in,       UVM_DEFAULT)
        `uvm_field_int (data_out,      UVM_DEFAULT)
        `uvm_field_int (valid,         UVM_DEFAULT)
        `uvm_field_int (done,          UVM_DEFAULT)        
    `uvm_object_utils_end
    
endclass : convDW_transaction

//////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
// CONVDW_SEQUENCE ///////////////////////////////////////////////////////////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////

class convDW_std_seq extends conv1_std_seq#(
                                            .pWEIGHT_BASE_ADDR (shared_pkg::pWEIGHT_BASE_ADDR),
                                            .pIN_CHANNEL       (convDW_pkg::pIN_CHANNEL),
                                            .pOUT_CHANNEL      (convDW_pkg::pOUT_CHANNEL),
                                            .pINPUT_WIDTH      (convDW_pkg::pINPUT_WIDTH),
                                            .pINPUT_HEIGHT     (convDW_pkg::pINPUT_HEIGHT),
                                            .pULTRA_RAM_NUM    (convDW_pkg::pULTRA_RAM_NUM),
                                            .pBLOCK_RAM_NUM    (convDW_pkg::pBLOCK_RAM_NUM),
                                            .pKERNEL_NUM       (convDW_pkg::pKERNEL_NUM),
                                            .pBIAS_NUM         (convDW_pkg::pBIAS_NUM),
                                            .pDEQUANT_SCALE_NUM(convDW_pkg::pDEQUANT_SCALE_NUM),
                                            .pWEIGHTS_NUM      (convDW_pkg::pWEIGHTS_NUM),
                                            .weight_path       (convDW_pkg::weight_path), 
                                            .image_path        (convDW_pkg::image_path),
                                            .pZEROPOINT_LOAD   (2),
                                            .T_TRANS           (convDW_transaction));

    // Register to Factory
    `uvm_object_utils(convDW_std_seq)            
    
    // Constructor
    function new(input string path = "convDW_std_seq");
        super.new(path);
    endfunction
       
    // Create Data Sequence Method
    task create_data_seq(convDW_transaction tr);                              
        gen_convDW_input_and_rslt();                           // Call C routine
        $readmemh(image_path, in_fm);                         // Read image to array                                           
        for(int i = 0; i < trans_amount; i++) begin           // Create seq items
            start_item(tr);
                tr.op           = LOAD_PIXELS;                            
                tr.rst          = 1'b0;                
                tr.load_weight  = 1'b0;                
                tr.en           = 1'b1;           
                tr.data_in      = in_fm[i];     
                `uvm_info("STD_SEQ", $sformatf("[No.%0d] Transaction Generated: data_in = %0h", i, tr.data_in), UVM_NONE)
            finish_item(tr);
        end
    endtask    
    
endclass : convDW_std_seq

//////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
// CONVDW_DRIVER /////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////

class convDW_driver extends uvm_driver#(convDW_transaction);
    // Register to Factory
    `uvm_component_utils(convDW_driver)
    
    // Properties       
    convDW_transaction tr;
    virtual convDW_if vif;
    
    // Constructor
    function new(input string path = "DRV_CONVDW", uvm_component parent = null);
        super.new(path, parent);
    endfunction
    
    // Build Phase
    virtual function void build_phase(uvm_phase phase);
        super.build_phase(phase);
        tr = convDW_transaction::type_id::create("tr");
        if(!uvm_config_db#(virtual convDW_if)::get(this, "", "cdw_vif", vif))
            `uvm_error("DRV_CONVDW", "UNABLE TO ACCESS THE INTERFACE!!!")
    endfunction
    
    // Run phase
    virtual task run_phase(uvm_phase phase);
        drive();
    endtask
    
    // Methods
    virtual task drive();
        reset_DUT();
        forever begin
            seq_item_port.get_next_item(tr);   
                    vif.op           <= tr.op;
                    vif.rst          <= tr.rst; 
                    vif.load_weight  <= tr.load_weight;                             
                if(tr.load_weight) begin
                    vif.weight_addr  <= tr.weight_addr; 
                    vif.weight_data  <= tr.weight_data;
                    vif.data_in      <= 'dx;
                    vif.en           <= 1'b0;                                        
                    @(posedge vif.clk);  
                    `uvm_info("DRV", $sformatf("[%s] Weight Loaded: weight_addr = %0h , weight_data = %16h", tr.op.name, tr.weight_addr, tr.weight_data), UVM_NONE)
                end 
                else if(!tr.load_weight) begin
                    vif.weight_addr  <= 'dx;
                    vif.weight_data  <= 'dx;
                    vif.en           <= tr.en;
                    vif.data_in      <= tr.data_in;
                    tr.tr_display("DRV");
                    @(posedge vif.clk);
                end
                `uvm_info("DRV_DEBUG", "Before item_done(tr)", UVM_NONE)
            seq_item_port.item_done(tr);
            `uvm_info("DRV_DEBUG", "After item_done(tr)", UVM_NONE)
        end
    endtask
    
    
    // DUT reset
    virtual task reset_DUT();
        repeat(5) begin 
            vif.op  <= RESET;
            vif.rst <= 1'b1;
            @(posedge vif.clk);
        end
        `uvm_info("DRV", "SYSTEM RESET: START OF SIMULATION", UVM_NONE)
    endtask
endclass : convDW_driver

//////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
// CONVDW_MONITOR ////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////

class convDW_monitor extends uvm_monitor;
    // Register to Factory
    `uvm_component_utils(convDW_monitor)
    
    // Properties   
    convDW_transaction tr;
    virtual convDW_if vif;  
    int valid_count = 0;  
    
    // Analysis Port
    uvm_analysis_port #(convDW_transaction) send;
    
    // Constructor
    function new(input string path = "MON", uvm_component parent = null);
        super.new(path, parent);
    endfunction
    
    // Build Phase
    virtual function void build_phase(uvm_phase phase);
        super.build_phase(phase);
        tr = convDW_transaction::type_id::create("tr");
        if(!uvm_config_db#(virtual convDW_if)::get(this, "", "cdw_vif", vif))
            `uvm_error("MON", "UNABLE TO ACCESS THE INTERFACE!!!");
        send = new("send", this);
    endfunction
    
    // Run phase
    virtual task run_phase(uvm_phase phase);
        phase.raise_objection(this);        
        forever begin
            @(posedge vif.clk);           
            tr.op = vif.op;         
            if(tr.op == RESET) begin
                tr.rst = 1'b1;
                `uvm_info("MON", "SYSTEM RESET DETECTED", UVM_NONE);
            end 
            else begin
                    tr.rst          = 1'b0;
                    tr.load_weight  = vif.load_weight;  
                    tr.en           = vif.en;                     
                if(vif.done)                                          
                    phase.drop_objection(this);                       // Stop Run Phase when DUT done                       
                else if(vif.load_weight) begin                        // weight load process
                    tr.weight_addr  = vif.weight_addr;
                    tr.weight_data  = vif.weight_data;
                    tr.data_in      = 'dx;
                    `uvm_info("MON", $sformatf("[%s] Weight Loaded: weight_addr = %0h , weight_data = %16h", tr.op.name, tr.weight_addr, tr.weight_data), UVM_NONE)
                end 
                else if(!vif.load_weight) begin                       // pe_conv_mac process                            
                    tr.data_in      = vif.data_in;
                    tr.data_out     = vif.data_out;
                    tr.valid        = vif.valid;                    
                    tr.done         = vif.done;                                        
                end                                                      
            end            
            // Send to Scoreboard
            send.write(tr);
            // Stop Run Phase
            if(tr.valid) begin
                valid_count = valid_count + 1;
                tr.tr_display("MON");
                `uvm_info("MON", $sformatf("No. Valid : %0d", valid_count), UVM_NONE)
            end                       
        end
    endtask: run_phase 
    
endclass : convDW_monitor

//////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
// CONVDW_AGENT //////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////

class convDW_agent extends conv1_agent#(.T_TRANS   (convDW_transaction),
                                        .T_DRIVER  (convDW_driver),
                                        .T_MONITOR (convDW_monitor));
    // Register to Factory
    `uvm_component_utils(convDW_agent)         
    
    // Constructor
    function new(input string path = "AGENT_CONVDW", uvm_component parent = null);
        super.new(path, parent);       
    endfunction
        
endclass : convDW_agent

//////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
// CONVDW_SCOREBOARD /////////////////////////////////////////////////////////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////

class convDW_scoreboard extends conv1_scoreboard#(.T_TRANS       (convDW_transaction        ),                                                   
                                                  .pDATA_WIDTH   (shared_pkg::pDATA_WIDTH   ),
                                                  .pINPUT_WIDTH  (convDW_pkg::pINPUT_WIDTH  ),
                                                  .pINPUT_HEIGHT (convDW_pkg::pINPUT_HEIGHT ),
                                                  .pIN_CHANNEL   (convDW_pkg::pIN_CHANNEL   ),
                                                  .pOUT_CHANNEL  (convDW_pkg::pOUT_CHANNEL  ),
                                                  .pKERNEL_SIZE  (convDW_pkg::pKERNEL_SIZE  ),
                                                  .pPADDING      (convDW_pkg::pPADDING      ),
                                                  .pSTRIDE       (convDW_pkg::pSTRIDE       ),
                                                  .pOUTPUT_WIDTH (convDW_pkg::pOUTPUT_WIDTH ),
                                                  .pOUTPUT_HEIGHT(convDW_pkg::pOUTPUT_HEIGHT),        
                                                  .img_data_path (convDW_pkg::img_data_path ),
                                                  .result_path   (convDW_pkg::result_path   ));             
            
    // Field Macro
    `uvm_component_utils(convDW_scoreboard)            
            
    // Constructor
    function new(input string path = "CONVDW_SCB", uvm_component parent = null);
        super.new(path, parent);        
    endfunction
    
endclass : convDW_scoreboard

//////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
// CONVDW_ENV ////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////

class convDW_env extends conv1_env#(.T_SCOREBOARD ( convDW_scoreboard ),
                                    .T_AGENT      ( convDW_agent      ));
    // Register to Factory
    `uvm_component_utils(convDW_env)
    
    // Constructor
    function new(input string path = "ENV_CONVDW", uvm_component parent = null);
        super.new(path, parent);       
    endfunction
        
endclass : convDW_env

//////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
// UVM TESTS /////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////

class shuffleNet_test extends uvm_test;
    // Register to Factory
    `uvm_component_utils(shuffleNet_test)
    
    // Properties
    conv1_env e;
    conv1_std_seq ss;
    int log_file;
    string report_path = "/home/hao/Documents/0.KHOA_LUAN_TOT_NGHIEP/shuffle_net/ShuffleNet_Evaluation/conv1_output/uvm_report/conv1_report.txt";
    
    // Constructor
    function new(input string path = "TEST", uvm_component parent = null);
        super.new(path, parent);       
    endfunction
    
    // Build Phase
    virtual function void build_phase(uvm_phase phase);
        super.build_phase(phase);
        e  = conv1_env::type_id::create("e", this);
        ss = conv1_std_seq::type_id::create("ss");   
    endfunction
    
    // Run Phase
    virtual task run_phase(uvm_phase phase);
        log_file = $fopen(report_path);
        uvm_top.set_report_default_file_hier(log_file);
        uvm_top.set_report_severity_action_hier (UVM_INFO, UVM_DISPLAY | UVM_LOG);
        phase.raise_objection(this);
            ss.start(e.a.seqr);
        phase.drop_objection(this);
    endtask
    
    // End of Elaboration Phase
    function void end_of_elaboration_phase(uvm_phase phase);
        uvm_phase main_phase;
        super.end_of_elaboration_phase(phase);
        main_phase = phase.find_by_name("main", 0);
        main_phase.phase_done.set_drain_time(this, 500);
    endfunction
endclass : shuffleNet_test


class shuffleNet_test2 extends uvm_test;
    // Register to Factory
    `uvm_component_utils(shuffleNet_test2)
    
    // Properties
    convDW_env e;
    convDW_std_seq ss;
    int log_file;
    string report_path = "/home/hao/Documents/0.KHOA_LUAN_TOT_NGHIEP/shuffle_net/ShuffleNet_Evaluation/convDW_output/uvm_report/convDW_report.txt";
    
    // Constructor
    function new(input string path = "TEST2", uvm_component parent = null);
        super.new(path, parent);       
    endfunction
    
    // Build Phase
    virtual function void build_phase(uvm_phase phase);
        super.build_phase(phase);                                               
        e  = convDW_env::type_id::create("e", this);
        ss = convDW_std_seq::type_id::create("ss");   
    endfunction
    
    // Run Phase
    virtual task run_phase(uvm_phase phase);
        log_file = $fopen(report_path);
        uvm_top.set_report_default_file_hier(log_file);
        uvm_top.set_report_severity_action_hier (UVM_INFO, UVM_DISPLAY | UVM_LOG);
        phase.raise_objection(this);
            ss.start(e.a.seqr);
        phase.drop_objection(this);
    endtask
    
    // End of Elaboration Phase
    function void end_of_elaboration_phase(uvm_phase phase);
        uvm_phase main_phase;
        super.end_of_elaboration_phase(phase);
        main_phase = phase.find_by_name("main", 0);
        main_phase.phase_done.set_drain_time(this, 500);
    endfunction
endclass : shuffleNet_test2

//////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
// TOP TESTBENCH /////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////

module ShuffleNet_UVM_TB;

// INSTANCES
    conv1_if c1_vif();  
    convDW_if cdw_vif();                           
    logic CLK;
        
    IP_Conv1 #(                             
        .pDATA_WIDTH        (shared_pkg::pDATA_WIDTH),    
        .pINPUT_WIDTH       (conv1_pkg::pINPUT_WIDTH),
        .pINPUT_HEIGHT      (conv1_pkg::pINPUT_HEIGHT),    
        .pWEIGHT_DATA_WIDTH (shared_pkg::pWEIGHT_DATA_WIDTH),
        .pWEIGHT_BASE_ADDR  (shared_pkg::pWEIGHT_BASE_ADDR),    
        .pIN_CHANNEL        (conv1_pkg::pIN_CHANNEL),
        .pOUT_CHANNEL       (conv1_pkg::pOUT_CHANNEL),    
        .pKERNEL_SIZE       (conv1_pkg::pKERNEL_SIZE),
        .pPADDING           (conv1_pkg::pPADDING),
        .pSTRIDE            (conv1_pkg::pSTRIDE),
        .pOUTPUT_PARALLEL   (conv1_pkg::pOUTPUT_PARALLEL),    
        .pACTIVATION        (conv1_pkg::pACTIVATION)
    ) DUT_CONV1 (    
        .clk         (c1_vif.clk),
        .rst         (c1_vif.rst),
        .en          (c1_vif.en),
        .load_weight (c1_vif.load_weight),
        .weight_addr (c1_vif.weight_addr),
        .weight_data (c1_vif.weight_data),
        .data_in     (c1_vif.data_in),    
        .data_out    (c1_vif.data_out),
        .valid       (c1_vif.valid),
        .done        (c1_vif.done)
    );
    
    IP_ConvDW #(
        .pDATA_WIDTH         (shared_pkg::pDATA_WIDTH)
        ,.pINPUT_WIDTH       (convDW_pkg::pINPUT_WIDTH)
        ,.pINPUT_HEIGHT      (convDW_pkg::pINPUT_HEIGHT)
        ,.pWEIGHT_DATA_WIDTH (shared_pkg::pWEIGHT_DATA_WIDTH)
        ,.pWEIGHT_BASE_ADDR  (shared_pkg::pWEIGHT_BASE_ADDR)
        ,.pIN_CHANNEL        (convDW_pkg::pIN_CHANNEL)
        ,.pOUT_CHANNEL       (convDW_pkg::pOUT_CHANNEL)
        ,.pKERNEL_SIZE       (convDW_pkg::pKERNEL_SIZE)
        ,.pPADDING           (convDW_pkg::pPADDING)
        ,.pSTRIDE            (convDW_pkg::pSTRIDE)
        ,.pOUTPUT_PARALLEL   (convDW_pkg::pOUTPUT_PARALLEL)
        ,.pACTIVATION        (convDW_pkg::pACTIVATION)
    ) DUT_CONVDW (    
        .clk         (cdw_vif.clk),
        .rst         (cdw_vif.rst),
        .en          (cdw_vif.en),
        .load_weight (cdw_vif.load_weight),
        .weight_addr (cdw_vif.weight_addr),
        .weight_data (cdw_vif.weight_data),
        .data_in     (cdw_vif.data_in),
        .data_out    (cdw_vif.data_out),
        .valid       (cdw_vif.valid),
        .done        (cdw_vif.done)
    );
    
    // Clock generating
    initial CLK = 1'b0;        
    always #10 CLK = ~CLK;    
    assign c1_vif.clk  = CLK;
    assign cdw_vif.clk = CLK;
    
    // Run Tests
    initial begin
        uvm_config_db #(virtual conv1_if)::set(null, "*", "vif", c1_vif);
        uvm_config_db #(virtual convDW_if)::set(null, "*", "cdw_vif", cdw_vif);
        run_test("shuffleNet_test2");
    end

endmodule