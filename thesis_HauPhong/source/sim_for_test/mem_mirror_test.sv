`timescale 1ns / 1ps

typedef logic [63:0] ultra_ram [];
typedef logic [63:0] ultra_ram_queue [$];
typedef enum bit[3:0] { RESET,  
                        MEM_KERNEL_LOAD,
                        MEM_BIAS_LOAD,
                        MEM_SCALE_LOAD,
                        DATA_IN_LOAD} oper_mode;

module mem_mirror_test;
    ultra_ram kernel_mem [logic]; 
    ////////////////////////////////
    ultra_ram_queue virtual_mem [int];
    oper_mode op = MEM_KERNEL_LOAD; 
    logic [31:0] weight_addr = 32'h4000_0000;
    logic [63:0] weight_data;
    
    int a;
    
    initial begin
        for(int i = weight_addr; i < weight_addr + 25; i++) begin
            if(i < weight_addr + 9) begin
                repeat(4) begin
                    weight_data = $random();
                    virtual_mem[i].push_back(weight_data);
                end
            end else begin
                weight_data = $random();
                virtual_mem[i].push_back(weight_data);
            end
        end
        
        
        foreach(virtual_mem[i]) begin
            $write("key: %0h ,", i);
            foreach(virtual_mem[i][j]) begin
                $write("  { pos : %0d  data = %16h }  ", j, virtual_mem[i][j]);
            end
            $write("\n");    
        end 
        $display("%p", virtual_mem);
        
    end
    
    
    
    // Randomize mem with correct structure
    function randomize_mem;
         // initialize
        for(int i = 0;  i < 30; i++) begin
            if(i < 9) begin
                kernel_mem[i] = new[4];
            end else begin
                kernel_mem[i] = new[1];
            end
        end
        
        // give random value
        foreach(kernel_mem[i]) begin
            foreach(kernel_mem[i][j]) begin
                kernel_mem[i][j] = $random;
                $display("address : %2d , pos : %0d , random_data_value : %16h", i, j, kernel_mem[i][j]);
            end
        end
        $display();
        
        // traverse through memory
        foreach(kernel_mem[i]) begin
            $write("key: %2d ,", i);
            foreach(kernel_mem[i][j]) begin
                $write("  { pos : %0d  data = %16h }  ", j, kernel_mem[i][j]);
            end
            $write("\n");
        end
    endfunction
endmodule
