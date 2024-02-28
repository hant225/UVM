`timescale 1ns / 1ps
`include "uvm_macros.svh"
import uvm_pkg::*;


////////////////////////////////////////////////////////////////////////
class driver extends uvm_driver;
    `uvm_component_utils(driver);
    
    function new(string path, uvm_component parent);
        super.new(path, parent);
    endfunction
    
    task run();
        `uvm_info("DRV1", "Executed Driver1 Code", UVM_HIGH);
        `uvm_info("DRV2", "Executed Driver2 Code", UVM_HIGH);
    endtask
    
endclass

////////////////////////////////////////////////////////////////////////
class monitor extends uvm_monitor;
    `uvm_component_utils(monitor);
    
    function new(string path, uvm_component parent);
        super.new(path, parent);
    endfunction
    
    task run();
        `uvm_info("MON", "Executed Monitor code", UVM_HIGH);
    endtask
endclass

////////////////////////////////////////////////////////////////////////
class env extends uvm_env;
    `uvm_component_utils(env);
    
    driver drv;
    monitor mon;
    
    function new(string path, uvm_component parent);
        super.new(path, parent);
    endfunction
    
    task run();
        drv = new("DRV", this);
        mon = new("MON", this);
        drv.run();
        mon.run();
    endtask
endclass

////////////////////////////////////////////////////////////////////////
module section2_16;

    env e;
    
    initial begin
        e = new("ENV", null);
        e.set_report_verbosity_level_hier(UVM_HIGH);    // change default verbosity of entire hierachy to HIGH
        e.run();
    end

endmodule
