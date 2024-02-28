`timescale 1ns/1ns
`include "uvm_macros.svh"
import uvm_pkg::*;

//////////////////////////////////////////////////////////////////////////////////

class l103_driver extends uvm_driver;
    // Register to Factory
    `uvm_component_utils(l103_driver)
    
    // Constructor
    function new(string path = "l103_driver", uvm_component parent = null);
        super.new(path, parent);
    endfunction
    
    // Reset Phases
    task reset_phase(uvm_phase phase);
        phase.raise_objection(this);
        `uvm_info("driver", "Driver Reset Started", UVM_NONE);
        #100;    
        `uvm_info("driver", "Driver Reset Ended", UVM_NONE);
        phase.drop_objection(this);
    endtask
    
    // Main Phases
    task main_phase(uvm_phase phase);
        phase.raise_objection(this);
        `uvm_info("driver", "Driver Main Phase Started", UVM_NONE);
        #100;    
        `uvm_info("driver", "Driver Main Phase Ended", UVM_NONE);
        phase.drop_objection(this);
    endtask
endclass

//////////////////////////////////////////////////////////////////////////////////

class l103_monitor extends uvm_monitor;
    // Register to Factory
    `uvm_component_utils(l103_monitor)
    
    // Constructor
    function new(string path = "l103_monior", uvm_component parent = null);
        super.new(path, parent);
    endfunction
    
    // Reset Phases
    task reset_phase(uvm_phase phase);
        phase.raise_objection(this);
        `uvm_info("mon", "Monitor Reset Started", UVM_NONE);
        #300;    
        `uvm_info("mon", "Monitor Reset Ended", UVM_NONE);
        phase.drop_objection(this);
    endtask
    
    // Main Phases
    task main_phase(uvm_phase phase);
        phase.raise_objection(this);
        `uvm_info("mon", "Monitor Main Phase Ended", UVM_NONE);
        #400;    
        `uvm_info("mon", "Monitor Main Phase Completed", UVM_NONE);
        phase.drop_objection(this);
    endtask
endclass

//////////////////////////////////////////////////////////////////////////////////

class l103_env extends uvm_env;
    // Register to Factory
    `uvm_component_utils(l103_env)
    
    // Properties
    l103_driver  d;
    l103_monitor m;
    
    // Constructor
    function new(string path = "l103_env", uvm_component parent = null);
        super.new(path, parent);
    endfunction
    
    // Build Phase
    virtual function void build_phase(uvm_phase phase);
        super.build_phase(phase);
        `uvm_info("env", "Env Build Phase Executed", UVM_NONE)
        d = l103_driver::type_id::create("driver", this);
        m = l103_monitor::type_id::create("monitor", this);
    endfunction
endclass

//////////////////////////////////////////////////////////////////////////////////

class l103_test extends uvm_component;
    // Register to Factory
    `uvm_component_utils(l103_test)
    
    // Properties
    l103_env e;    
        
    // Constructor
    function new(string path = "l103_test", uvm_component parent = null);
        super.new(path, parent);
    endfunction
    
    // Build Phase
    virtual function void build_phase(uvm_phase phase);
        super.build_phase(phase);
        `uvm_info("test", "Test Build Phase Executed", UVM_NONE)
        e = l103_env::type_id::create("env", this);
    endfunction
endclass

//////////////////////////////////////////////////////////////////////////////////

module section6_103;
    initial begin
        run_test("l103_test");
    end
endmodule
