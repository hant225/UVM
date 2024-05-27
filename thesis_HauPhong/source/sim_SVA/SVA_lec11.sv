`timescale 1ns / 1ps


module SVA_lec11;

    reg clk = 0;
    reg rst = 0;
    reg wr = 0;
    reg rd = 0;
    reg temp = 0;
    
    integer i = 0, j = 0;
    integer hitwr = 0, hitrd = 0,err = 0;

    initial begin
        #2  temp = 1;
        #10 temp = 0;
    end

    initial begin
        #0  rst = 1;
        #20 rst = 0;
        #30 rst = 1; 
    end
    
    initial begin
        #40 wr = 1;
        #10 wr = 0;
    end
    
    initial begin
        #60 rd = 1;
        #10 rd = 0;
    end
    
    always #5 clk = ~clk;
        
    task checkreset();
        repeat(2) @(posedge clk);       // reset zone
        for(i = 0; i < 10; i++) begin   // check if rst is toggle after first 2 cycles
            @(posedge clk);
            if(rst == 1'b1)
                err++;
        end
    endtask
    
    task hit();
        repeat(2) @(posedge clk);       
        for(j = 0; j < 10; j++) begin   
            @(posedge clk);
            if(!rst && wr)
                hitwr++;
            if(!rst && rd)
                hitrd++;            
        end
    endtask
    
    // VERILOG -----------------------------------------
    initial begin
        fork
            checkreset();
            hit();
        join
        
        if(err == 0 && hitwr > 0 && hitrd > 0)
            $display("[VERILOG] Success at %0t", $time);
        else
            $display("[VERILOG] Failure at %0t", $time);
    end
    
    // ASSERTION -----------------------------------------
    assert property (@(posedge clk) $rose(temp) |-> ##2 !rst throughout (wr[->1] and rd[->1])) $info("[SVA] Success at %0t", $time);    
    
    initial begin
        #120 $finish;
    end
endmodule







