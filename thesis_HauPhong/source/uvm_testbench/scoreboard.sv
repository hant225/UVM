`timescale 1ns / 1ps
`include "uvm_macros.svh"
import uvm_pkg::*;

//////////////////////////////////////////////////////////////////////////////////

typedef logic [63:0] ultra_ram_queue [$:4];

class scoreboard extends uvm_monitor;
    // Register to Factory
    `uvm_component_utils(scoreboard)
   
    // Properties - Mem Mirror
    ultra_ram_queue virtual_mem [int];
    int i_weight_addr;
    logic [63:0] modified_weight_data;
    // Properties - File Handle
    int fd;
    string virtual_mem_path = "/home/hao/Documents/0.KHOA_LUAN_TOT_NGHIEP/log_dir/virtual_mem.txt";
    string file_header = "\
    \n+==============================================================================================================================================================================+\
    \n                                                         SCOREBOARD'S VIRTUAL MEMORY                                                                                                  \
    \n+==============================================================================================================================================================================+\n\
    ";
    // Properties - Result Evaluation
    transaction result_q [$]; 
    int filter_num  = 32;
    int kernel_size = 9;
    logic [31:0] arr_adder_tree [32];    
    
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
    
    // Extract Phase
    virtual function void extract_phase(uvm_phase phase);
        super.extract_phase(phase);
        `uvm_info("SCB", $sformatf("\nSIMULATION FINISHED! Number of collected results : %0d\n", this.result_q.size()), UVM_NONE)
        foreach(this.result_q[i]) begin
            `uvm_info("SCB_DEBUG", $sformatf("Result Queue size = %0d", result_q.size()), UVM_NONE)
            `uvm_info("SCB", $sformatf("Result No.%0d", i), UVM_NONE)
            `uvm_info("SCB", this.result_q[i].sprint(), UVM_NONE)
        end
    endfunction
    
    // Check Phase
    virtual function void check_phase(uvm_phase phase);
        super.check_phase(phase);
        `uvm_info("SCB", "[CHECK PHASE] START CHECKING PROCESS\n", UVM_NONE)
        eval_rslt();
    endfunction
    
    // Write Method
    virtual function void write(transaction tr);
        if(tr.op == RESET)
            reset_state();
        else if (tr.op == MEM_KERNEL_LOAD || tr.op == MEM_BIAS_LOAD || tr.op == MEM_SCALE_LOAD)  
            mirror_mem(tr); 
        else
            collect_dut_result(tr);
    endfunction   
    
    // Reset Method
    function void reset_state();
        `uvm_info("SCB", "SYSTEM RESET", UVM_NONE)
        fd = $fopen(virtual_mem_path, "w");
        if(fd) begin
            `uvm_info("SCB", $sformatf("VIRTUAL MEMORY FILE READY TO WRITE: %s", virtual_mem_path),UVM_NONE)
            $fdisplay(fd, "%s", file_header);
        end else    
            `uvm_error("SCB", "UNABLE TO CREATE VIRTUAL MEMORY FILE!")
        $fclose(fd);
    endfunction
    
    // Mirroring Ram Method
    ///////////////// DELETE LATER START /////////////////////////////
    ///////////////// DELETE LATER START /////////////////////////////
    ///////////////// DELETE LATER START /////////////////////////////
    function create_mem_for_test();
        int fd_tmp;    
        string mem_for_test_path = "/home/hao/Documents/0.KHOA_LUAN_TOT_NGHIEP/log_dir/mem_for_test.txt";
        fd_tmp = $fopen(mem_for_test_path, "w");
        if(!fd_tmp) `uvm_error("SCB", "UNABLE TO OPEN FILE TO WRITE")
        foreach(virtual_mem[i]) begin
            foreach(virtual_mem[i][j]) begin
                $fwrite(fd_tmp, "%h\n", virtual_mem[i][j]);
            end
        end
        $fclose(fd_tmp);
    endfunction
    ///////////////// DELETE LATER END   /////////////////////////////
    ///////////////// DELETE LATER END   /////////////////////////////
    ///////////////// DELETE LATER END   /////////////////////////////
    function void mirror_mem(transaction tr);
        `uvm_info("SCB", $sformatf("[MEMORY LOADING] Weight Loaded: weight_addr = %0h , weight_data = %8h_%8h", tr.weight_addr, tr.weight_data[63:32], tr.weight_data[31:0]), UVM_NONE)
        // manipulate weight data to write
        i_weight_addr = tr.weight_addr;                                 // convert logic to int
        modified_weight_data[63:32] = tr.weight_data[31:0];
        modified_weight_data[31:0]  = tr.weight_data[63:32];
        virtual_mem[i_weight_addr].push_back(modified_weight_data);     // push to queue
        
        // write to file if load scale (last to load)
        if(tr.op == MEM_SCALE_LOAD) begin            
            fd = $fopen(virtual_mem_path, "a+");
            if(!fd) `uvm_error("SCB", "UNABLE TO OPEN FILE TO WRITE")
            else begin
                foreach(virtual_mem[i]) begin
                    $fwrite(fd, "address: %0h ,", i);
                    foreach(virtual_mem[i][j]) begin
                        $fwrite(fd, "  { pos : %0d  data = %8h_%8h }  ", j, virtual_mem[i][j][63:32], virtual_mem[i][j][31:0]);
                        ///////////////// DELETE LATER START /////////////////////////////
                        create_mem_for_test();
                        ///////////////// DELETE LATER END   /////////////////////////////
                    end
                    $fwrite(fd, "\n");    
                end
            end    
            $fclose(fd);
            `uvm_info("SCB", $sformatf("VIRTUAL MEMORY FILE CREATED: %s\n\n", virtual_mem_path), UVM_NONE)
        end
    endfunction
    
    // Collect DUT's Results Method
    function void collect_dut_result(transaction tr);
        transaction deep_cp_obj = new;
        deep_cp_obj.data_in  = tr.data_in;
        deep_cp_obj.data_out = tr.data_out;
        tr.tr_display("SCB");
        result_q.push_back(deep_cp_obj);
    endfunction
    
    // Reference Model
    function eval_rslt();
        $display("Result queue list: ");
        foreach(result_q[i]) begin
            $display("%b", result_q[i].data_in);
        end
    endfunction
endclass

