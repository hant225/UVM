`timescale 1ns / 1ps
`include "uvm_macros.svh"
import uvm_pkg::*;

class driver1 extends uvm_driver;
    `uvm_component_utils(driver1)

    function new(string path, uvm_component parent);
        super.new(path, parent);
    endfunction

    task run();
        `uvm_info("DRV", "Infomation Message", UVM_NONE);   
        `uvm_warning("DRV", "Potential Error");
        `uvm_error("DRV", "Real Error") // uvm_count
        `uvm_error("DRV", "Second Real Error") // uvm_count
        /*                       
        #10;
        `uvm_fatal("DRV", "Simulation cannot continue DRV");        // uvm_exit
        #10;
        `uvm_fatal("DRV1", "Simulation cannot continues DRV1") 
        */
    endtask

endclass

module section2_22;
    driver1 drv;
    int file;
    string fpath = "/home/hao/Documents/0.KHOA_LUAN_TOT_NGHIEP/uvm_part1/log/log.txt";
    
    initial begin
        file = $fopen(fpath, "w"); 
        drv = new("DRV", null);
        // drv.set_report_severity_override(UVM_FATAL, UVM_ERROR);   // change all severity of UVM_FATAL to UVM_ERROR 
        // UVM_FATAL become UVM_ERROR after above code
        // we will get 2 UVM_ERROR report and the simulation won't finished by `uvm_fatal
//        drv.set_report_severity_id_override(UVM_FATAL, "DRV1",UVM_ERROR);
//        drv.set_report_severity_action(UVM_INFO, UVM_NO_ACTION);
//        drv.set_report_max_quit_count(2);
        
        
        // use the syntax below to store warning, error or info in a unique file
         drv.set_report_severity_file(UVM_ERROR, file);
        
        // use the syntax below to store all report into 1 file
//        drv.set_report_default_file(file);
//        drv.set_report_severity_action(UVM_INFO, UVM_DISPLAY | UVM_LOG);
//        drv.set_report_severity_action(UVM_WARNING, UVM_DISPLAY | UVM_LOG);
        drv.set_report_severity_action(UVM_ERROR, UVM_DISPLAY | UVM_LOG);
        
        drv.run();
        
        #10;
        $fclose(file);
    end
endmodule
