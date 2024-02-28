`timescale 1ns / 1ps
`include "uvm_macros.svh"
import uvm_pkg::*;

//////////////////////////////////////////////////////////////////////////////////

class comp1 extends uvm_component;
    // Register to Factory
    `uvm_component_utils(comp1)
    
    // Properties
    int data1 = 0;
    
    // Constructor
    function new(string path = "comp1", uvm_component parent);
        super.new(path, parent);
    endfunction
    
    // Build Phase
    virtual function void build_phase(uvm_phase phase);
        super.build_phase(phase);
        // if(!uvm_config_db#(int)::get(null, "uvm_test_top", "data", data1))
        if(!uvm_config_db#(int)::get(this, "", "data", data1))  // uvm_test_top.env.agent.comp1.data
            `uvm_error("comp1", "Unable to access Interface")
    endfunction
    
    // Run Phase
    virtual task run_phase(uvm_phase phase);
        phase.raise_objection(this);
            `uvm_info("comp1", $sformatf("Data rcvd comp1 : %0d", data1), UVM_NONE)
        phase.drop_objection(this);
    endtask
endclass

//////////////////////////////////////////////////////////////////////////////////

class comp2 extends uvm_component;
    // Register to Factory
    `uvm_component_utils(comp2)
    
    // Properties
    int data2 = 0;
    
    // Constructor
    function new(string path = "comp2", uvm_component parent);
        super.new(path, parent);
    endfunction
    
    // Build Phase
    virtual function void build_phase(uvm_phase phase);
        super.build_phase(phase);
        // if(!uvm_config_db#(int)::get(null, "uvm_test_top", "data", data2))
        if(!uvm_config_db#(int)::get(this, "", "data", data2))    // uvm_test_top.env.agent.comp2.data
            `uvm_error("comp2", "Unable to access Interface")
    endfunction
    
    // Run Phase
    virtual task run_phase(uvm_phase phase);
        phase.raise_objection(this);
            `uvm_info("comp2", $sformatf("Data rcvd comp2 : %0d", data2), UVM_NONE)
        phase.drop_objection(this);
    endtask
endclass

//////////////////////////////////////////////////////////////////////////////////

class l79_agent extends uvm_agent;
    // Register to Factory
    `uvm_component_utils(l79_agent)
    
    // Properties
    comp1 c1;
    comp2 c2;
    
    // Constructor
    function new(input string inst = "AGENT", uvm_component c);
        super.new(inst, c);
    endfunction
    
    // Build Phase
    virtual function void build_phase(uvm_phase phase);
        super.build_phase(phase);
        c1 = comp1::type_id::create("c1", this);
        c2 = comp2::type_id::create("c2", this);
    endfunction
endclass

//////////////////////////////////////////////////////////////////////////////////

class l79_env extends uvm_env;
    // Register to Factory
    `uvm_component_utils(l79_env)
    
    // Properties
    l79_agent a;
    
    // Constructor
    function new(input string inst = "ENV", uvm_component c);
        super.new(inst, c);
    endfunction
    
    // Build Phase
    virtual function void build_phase(uvm_phase phase);
        super.build_phase(phase);
        a = l79_agent::type_id::create("AGENT", this);
    endfunction 
endclass

//////////////////////////////////////////////////////////////////////////////////

class l79_test extends uvm_test;
    // Register to Factory
    `uvm_component_utils(l79_test)
    
    // Properties
    l79_env e;
    
    // Constructor
    function new(input string inst = "TEST", uvm_component c);
        super.new(inst, c);
    endfunction
    
    // Build Phase
    virtual function void build_phase(uvm_phase phase);
        super.build_phase(phase);
        e = l79_env::type_id::create("ENV", this);
    endfunction
endclass

//////////////////////////////////////////////////////////////////////////////////

module section5_79;
    int data = 256;
    
    initial begin
        uvm_config_db#(int)::set(null, "uvm_test_top.ENV.AGENT*", "data", data);   // uvm_test_top.data
        run_test("l79_test");
    end
endmodule













