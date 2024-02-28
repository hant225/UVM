`include "uvm_macros.svh"
import uvm_pkg::*;

//////////////////////////////////////////////////////////////////////////////////

class l109_driver extends uvm_driver;
    // Register to Factory
    `uvm_component_utils(l109_driver)

    // Constructor
    function new(string path = "l109_driver", uvm_component parent = null);
        super.new(path, parent);
    endfunction

    // Build Phase;
    virtual function void build_phase(uvm_phase phase);
        super.build_phase(phase);
    endfunction
    
    // Reset Phase
    task reset_phase(uvm_phase phase);
        phase.raise_objection(this);
            `uvm_info("drv", "Driver Reset Started", UVM_NONE);
            #100;
            `uvm_info("drv", "Driver Reset Ended", UVM_NONE);
        phase.drop_objection(this);
    endtask
    
    // Main Phase
    task main_phase(uvm_phase phase);
        phase.raise_objection(this);
            `uvm_info("drv", "Driver Main Started", UVM_NONE);
            #100;
            `uvm_info("drv", "Driver Main Ended", UVM_NONE);
        phase.drop_objection(this);
    endtask
    
    // Reset Phase
    task post_main_phase(uvm_phase phase);
        `uvm_info("drv", "Driver Post-Main Phase Started", UVM_NONE);    
    endtask
endclass

//////////////////////////////////////////////////////////////////////////////////

class l109_monitor extends uvm_monitor;
    // Register to Factory
    `uvm_component_utils(l109_monitor)

    // Constructor
    function new(string path = "l109_monitor", uvm_component parent = null);
        super.new(path, parent);
    endfunction

    // Build Phase;
    virtual function void build_phase(uvm_phase phase);
        super.build_phase(phase);
    endfunction
    
    // Reset Phase
    task reset_phase(uvm_phase phase);
        phase.raise_objection(this);
            `uvm_info("mon", "Monitor Reset Started", UVM_NONE);
            #150;
            `uvm_info("mon", "Monitor Reset Ended", UVM_NONE);
        phase.drop_objection(this);
    endtask
    
    // Main Phase
    task main_phase(uvm_phase phase);
        phase.raise_objection(this);
            `uvm_info("mon", "Monitor Main Started", UVM_NONE);
            #200;
            `uvm_info("mon", "Monitor Main Ended", UVM_NONE);
        phase.drop_objection(this);
    endtask
    
    // Reset Phase
    task post_main_phase(uvm_phase phase);
        `uvm_info("mon", "Monitor Post-Main Phase Started", UVM_NONE);    
    endtask
endclass

//////////////////////////////////////////////////////////////////////////////////

class l109_env extends uvm_env;
    // Register to Factory
    `uvm_component_utils(l109_env)
    
    // Properties
    l109_driver  d;
    l109_monitor m;

    // Constructor
    function new(string path = "l109_env", uvm_component parent = null);
        super.new(path, parent);
    endfunction

    // Build Phase;
    virtual function void build_phase(uvm_phase phase);
        super.build_phase(phase);
        d = l109_driver::type_id::create("d", this);
        m = l109_monitor::type_id::create("m", this);
    endfunction
endclass

//////////////////////////////////////////////////////////////////////////////////

class l109_test extends uvm_test;
    // Register to Factory
    `uvm_component_utils(l109_test)
    
    // Properties
    l109_env e;

    // Constructor
    function new(string path = "l109_test", uvm_component parent = null);
        super.new(path, parent);
    endfunction

    // Build Phase;
    virtual function void build_phase(uvm_phase phase);
        super.build_phase(phase);
        e = l109_env::type_id::create("e", this);
    endfunction
    
    // EoE Phase
    virtual function void end_of_elaboration_phase(uvm_phase phase);
        uvm_phase main_phase;
        super.end_of_elaboration_phase(phase);
          main_phase = phase.find_by_name("main", 0);
          main_phase.phase_done.set_drain_time(this, 100);
    endfunction
endclass

//////////////////////////////////////////////////////////////////////////////////

module section6_109;
    initial begin
        run_test("l109_test");
    end
endmodule

