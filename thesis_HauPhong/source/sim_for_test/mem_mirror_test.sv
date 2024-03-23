`timescale 1ns / 1ps

typedef logic [63:0] ultra_ram [];

module mem_mirror_test;
    ultra_ram kernel_mem [int];    
    
    initial begin
        // initialize
        for(int i = 0;  i < 30; i++) begin
            if(i < 9) begin
                kernel_mem[i] = new[4];
            end else begin
                kernel_mem[i] = new[1];
            end
        end
        
        // check size
        //  foreach(kernel_mem[i])
        //      $display("key = %0d , size = %0d", i, kernel_mem[i].size());
        
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
    end
endmodule
