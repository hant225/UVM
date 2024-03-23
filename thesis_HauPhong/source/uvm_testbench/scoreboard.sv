`timescale 1ns / 1ps
`include "uvm_macros.svh"
import uvm_pkg::*;

//////////////////////////////////////////////////////////////////////////////////

typedef logic [63:0] ultra_ram_queue [$:4];

class scoreboard extends uvm_monitor;
    // Register to Factory
    `uvm_component_utils(scoreboard)
   
    // Properties
    ultra_ram_queue virtual_mem [int];
    int i_weight_addr;
    logic [63:0] modified_weight_data;
    
    int fd;
    string virtual_mem_path = "/home/hao/Documents/0.KHOA_LUAN_TOT_NGHIEP/log_dir/virtual_mem.txt";
    string file_header = "\
    \n+-----------------------------+\
    \n| SCOREBOARD'S VIRTUAL MEMORY |\
    \n+-----------------------------+\n\
    ";

    // Analysis Imp
    uvm_analysis_imp #(transaction, scoreboard) recv;
    
    // Constructor
    function new(input string path = "SCB", uvm_component parent = null);
        super.new(path, parent);
    endfunction
    
    // Build Phase
    virtual function void build_phase(uvm_phase phase);
        super.build_phase(phase);
        recv = new("recv", this);
    endfunction
    
    // Write Method
    virtual function void write(transaction tr);
        if(tr.op == RESET)
            reset_state();
        else if (tr.op == MEM_KERNEL_LOAD || tr.op == MEM_BIAS_LOAD || tr.op == MEM_SCALE_LOAD)  
            mirror_mem(tr); 
        else
            checking_result(tr);
    endfunction   
    
    // Reset Method
    function void reset_state();
        `uvm_info("SCB", "SYSTEM RESET", UVM_NONE)
        fd = $fopen(virtual_mem_path, "w");
        if(fd) begin
            `uvm_info("SCB", "VIRTUAL MEMORY FILE CREATED!",UVM_NONE)
            $fdisplay(fd, "%s", file_header);
            $display("%s", file_header);
        end else    
            `uvm_error("SCB", "UNABLE TO CREATE VIRTUAL MEMORY FILE!")
        $fclose(fd);
    endfunction
    
    // Mirroring Ram Method
    function void mirror_mem(transaction tr);
        `uvm_info("SCB", $sformatf("[MEMORY MIRROR]  Weight Loaded: weight_addr = %0h , weight_data = %0h\n", tr.weight_addr, tr.weight_data), UVM_NONE);
        // manipulate weight data to write
        i_weight_addr = tr.weight_addr;                         // convert logic to int
        modified_weight_data[63:32] = tr.weight_data[31:0];
        modified_weight_data[31:0]  = tr.weight_data[63:32];
        virtual_mem[i_weight_addr].push_back(modified_weight_data);   // push to queue
        
        // write to file if load scale (last to load)
        if(tr.op == MEM_SCALE_LOAD) begin            
            fd = $fopen(virtual_mem_path, "a+");
            if(!fd) `uvm_error("SCB", "UNABLE TO OPEN FILE TO WRITE")
            else begin
                foreach(virtual_mem[i]) begin
                    $fwrite(fd, "address: %0h ,", i);
                    foreach(virtual_mem[i][j]) begin
                        $fwrite(fd, "  { pos : %0d  data = %8h_%8h }  ", j, virtual_mem[i][j][63:32], virtual_mem[i][j][31:0]);
                    end
                    $fwrite(fd, "\n");    
                end
            end    
            $fclose(fd);
        end
    endfunction
    
    // Result Checking Method
    function void checking_result(transaction tr);
        $display("CHECKING RESULT HERE");
        sdisplay(tr);
    endfunction
    
    // Display Method
    function void sdisplay(transaction tr);
        `uvm_info("SCB", "--------------------------------------Transaction Info--------------------------------------", UVM_NONE)
        `uvm_info("SCB", $sformatf("op          = %s", tr.op.name), UVM_NONE)
        `uvm_info("SCB", $sformatf("rst         = %0h", tr.rst), UVM_NONE)
        `uvm_info("SCB", $sformatf("clr         = %0h", tr.clr), UVM_NONE)
        `uvm_info("SCB", $sformatf("load_weight = %0h", tr.load_weight), UVM_NONE)
        `uvm_info("SCB", $sformatf("en          = %0h", tr.en), UVM_NONE)
        `uvm_info("SCB", $sformatf("adder_en    = %0h", tr.adder_en), UVM_NONE)
        `uvm_info("SCB", $sformatf("dequant_en  = %0h", tr.dequant_en), UVM_NONE)
        `uvm_info("SCB", $sformatf("bias_en     = %0h", tr.bias_en), UVM_NONE)
        `uvm_info("SCB", $sformatf("act_en      = %0h", tr.act_en), UVM_NONE)
        `uvm_info("SCB", $sformatf("quant_en    = %0h", tr.quant_en), UVM_NONE)
        `uvm_info("SCB", $sformatf("weight_addr = %0h", tr.weight_addr), UVM_NONE)
        `uvm_info("SCB", $sformatf("weight_data = %0h  (Scale if load_weight = 0)", tr.weight_data), UVM_NONE)
        `uvm_info("SCB", $sformatf("data_in     = %0h", tr.data_in), UVM_NONE)
        `uvm_info("SCB", $sformatf("kernel_addr = %0h", tr.kernel_addr), UVM_NONE)
        `uvm_info("SCB", $sformatf("data_out    = %0h", tr.data_out), UVM_NONE)
        `uvm_info("SCB", "--------------------------------------------------------------------------------------------", UVM_NONE)
    endfunction
endclass


