`timescale 1ns / 1ps
`include "uvm_macros.svh"
import uvm_pkg::*;

//////////////////////////////////////////////////////////////////////////////////

class l94_driver extends uvm_driver;
    // Register to Factory
    `uvm_component_utils(l94_driver)
    
    // Constructor
    function new(string path = "l94_driver", uvm_component parent = null);
        super.new(path, parent);
    endfunction
    
    // Build Phase
    virtual function void build_phase(uvm_phase phase);
        super.build_phase(phase);
        `uvm_info("driver", "Driver Build Phase Executed", UVM_NONE)
    endfunction
    
    // Connect Phase
    virtual function void connect_phase(uvm_phase phase);
        super.connect_phase(phase);
        `uvm_info("driver", "Driver Connect Phase Executed", UVM_NONE)
    endfunction
endclass

//////////////////////////////////////////////////////////////////////////////////

class l94_monitor extends uvm_monitor;
    // Register to Factory
    `uvm_component_utils(l94_monitor)
    
    // Constructor
    function new(string path = "l94_monior", uvm_component parent = null);
        super.new(path, parent);
    endfunction
    
    // Build Phase
    virtual function void build_phase(uvm_phase phase);
        super.build_phase(phase);
        `uvm_info("monitor", "Monitor Build Phase Executed", UVM_NONE)
    endfunction
    
    // Connect Phase
    virtual function void connect_phase(uvm_phase phase);
        super.connect_phase(phase);
        `uvm_info("monitor", "Monitor Connect Phase Executed", UVM_NONE)
    endfunction
endclass

//////////////////////////////////////////////////////////////////////////////////

class l94_env extends uvm_env;
    // Register to Factory
    `uvm_component_utils(l94_env)
    
    // Properties
    l94_driver  d;
    l94_monitor m;
    
    // Constructor
    function new(string path = "l94_env", uvm_component parent = null);
        super.new(path, parent);
    endfunction
    
    // Build Phase
    virtual function void build_phase(uvm_phase phase);
        super.build_phase(phase);
        `uvm_info("env", "Env Build Phase Executed", UVM_NONE)
        d = l94_driver::type_id::create("driver", this);
        m = l94_monitor::type_id::create("monitor", this);
    endfunction
    
    // Connect Phase
    virtual function void connect_phase(uvm_phase phase);
        super.connect_phase(phase);
        `uvm_info("env", "Env Connect Phase Executed", UVM_NONE)
    endfunction
endclass

//////////////////////////////////////////////////////////////////////////////////

class l94_test extends uvm_component;
    // Register to Factory
    `uvm_component_utils(l94_test)
    
    // Properties
    l94_env e;    
        
    // Constructor
    function new(string path = "l94_test", uvm_component parent = null);
        super.new(path, parent);
    endfunction
    
    // Build Phase
    virtual function void build_phase(uvm_phase phase);
        super.build_phase(phase);
        `uvm_info("test", "Test Build Phase Executed", UVM_NONE)
        e = l94_env::type_id::create("env", this);
    endfunction
    
    // Connect Phase
    virtual function void connect_phase(uvm_phase phase);
        super.connect_phase(phase);
        `uvm_info("test", "Test Connect Phase Executed", UVM_NONE)
    endfunction
endclass

//////////////////////////////////////////////////////////////////////////////////


module section6_94;
    initial begin
        run_test("l94_test");
    end
endmodule
