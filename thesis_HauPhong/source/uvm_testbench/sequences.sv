`timescale 1ns / 1ps
`include "uvm_macros.svh"
import uvm_pkg::*;

//////////////////////////////////////////////////////////////////////////////////

class std_seq extends uvm_sequence#(transaction);   
    // Register to Factory
    `uvm_object_utils(std_seq)
    
    // Paramter
    localparam pBASE_WEIGHT_ADDR = 32'h4000_0000;
    localparam pKERNEL_NUM       = 9;
    localparam pBIAS_NUM         = 16;
    localparam pULTRA_RAM_NUM    = 4;
    localparam pBLOCK_RAM_NUM    = 16;
    
    // Properties   
    transaction tr;
    int no_cycles      = (pULTRA_RAM_NUM * pKERNEL_NUM) + pBLOCK_RAM_NUM + 1;              // (4 cycles * 9 channel) + 16 Bias + 1 for Scale
    int ultra_ram_pos  = 0;               // 4 ultra ram in total
    int trans_amount   = 10;
    logic [31:0] weight_addr = pBASE_WEIGHT_ADDR;
    
    // Constructor
    function new(input string path = "std_seq");
        super.new(path);
    endfunction
    
    // Body
    virtual task body();
        set_response_queue_error_report_disabled(1);
        tr = transaction::type_id::create("tr");
        do_load_weight(tr);
        `uvm_info("STD_SEQ", "Memory Weights Load Finished. Start Generating Transaction Data!", UVM_NONE)
        create_data_seq(tr);       
    endtask
    
    // Weight Load Method
    task do_load_weight(transaction tr);
        for(int i = 0; i < no_cycles; i++) begin
            start_item(tr);
            ///////////////////////////////////////////////////////////////                
                assert(tr.randomize());
                tr.rst          = 1'b0;
                tr.en           = 1'b0;
                tr.buffer_in_en = 1'b1;
                tr.load_weight  = 1'b1;
                tr.weight_addr  = this.weight_addr;     
        
                ultra_ram_pos++;
                if(i < pULTRA_RAM_NUM * pKERNEL_NUM) begin
                    tr.op = MEM_KERNEL_LOAD;
                    if(ultra_ram_pos == 4) begin
                        this.weight_addr = this.weight_addr + 32'h1;
                        ultra_ram_pos = 0;
                    end
                    `uvm_info("STD_SEQ", "----------------------------------[KERNEL LOADING]----------------------------------", UVM_NONE)
                end 
                else if (i != no_cycles - 1) begin
                    tr.op = MEM_BIAS_LOAD;
                    this.weight_addr = this.weight_addr + 32'h1;
                    `uvm_info("STD_SEQ", "----------------------------------[BIAS LOADING]----------------------------------", UVM_NONE)
                end else begin
                    tr.op = MEM_SCALE_LOAD;
                    this.weight_addr = this.weight_addr + 32'h1;
                    `uvm_info("STD_SEQ", "----------------------------------[SCALE LOADING]----------------------------------", UVM_NONE)
                end
            ///////////////////////////////////////////////////////////////
            finish_item(tr);   
        end
    endtask
    
    // Create Data Sequence Method
    task create_data_seq(transaction tr);
        tr.op = RUNNING; 
        for(int i = 0; i < trans_amount; i++) begin
            start_item(tr);
                assert(tr.randomize());                
                tr.rst          = 1'b0;
                tr.buffer_in_en = 1'b1;
                tr.en           = 1'b1;    
                tr.load_weight  = 1'b0;           
                `uvm_info("STD_SEQ", $sformatf("[No.%0d] Transaction Generated: data_in = %0h", i, tr.data_in), UVM_NONE)
            finish_item(tr);
        end
    endtask
endclass

