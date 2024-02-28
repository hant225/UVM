`timescale 1ns / 1ps
`include "uvm_macros.svh"
import uvm_pkg::*;

//////////////////////////////////////////////////////////////////////////////////

interface adder_if;
    logic [3:0] a;
    logic [3:0] b;
    logic [4:0] y;
endinterface

////////////////////////////////////////////////////////////////////////////////// DRIVER

class adder_drv extends uvm_driver;
    // Register to Factory
    `uvm_component_utils(adder_drv)
    
    // Properties
    virtual adder_if aif;
    
    // Constructor
    function new(string path = "drv", uvm_component parent = null);
        super.new(path, parent);
    endfunction
    
    // Build Phase
    virtual function void build_phase(uvm_phase phase);
        super.build_phase(phase);
        if(!uvm_config_db#(virtual adder_if)::get(this, "", "aif", aif))    // uvm_test_top.env.agent.drv.aif
            `uvm_error("drv", "Unable to access interface")
    endfunction
    
    // Run Phase
    virtual task run_phase(uvm_phase phase);
        phase.raise_objection(this);
            for(int i = 0; i < 10; i++) begin       // send 10 random stimulus to DUT
                aif.a <= $urandom;
                aif.b <= $urandom;
                #10;
            end
        phase.drop_objection(this);
    endtask
endclass

////////////////////////////////////////////////////////////////////////////////// AGENT

class adder_agent extends uvm_agent;
    // Register to Factory
    `uvm_component_utils(adder_agent)
    
    // Properties
    adder_drv d;
    
    // Constructor
    function new(string path = "agent", uvm_component parent = null);
        super.new(path, parent);
    endfunction
    
    // Build Phase
    virtual function void build_phase(uvm_phase phase);
        super.build_phase(phase);
        d = adder_drv::type_id::create("drv", this);
    endfunction
endclass

////////////////////////////////////////////////////////////////////////////////// ENVIRONMENT

class adder_env extends uvm_env;
    // Register to Factory
    `uvm_component_utils(adder_env)
    
    // Properties
    adder_agent a;
    
    // Constructor
    function new(string path = "env", uvm_component parent = null);
        super.new(path, parent);
    endfunction
    
    // Build Phase
    virtual function void build_phase(uvm_phase phase);
        super.build_phase(phase);
        a = adder_agent::type_id::create("agent", this);
    endfunction
endclass

////////////////////////////////////////////////////////////////////////////////// ENVIRONMENT

class adder_test extends uvm_test;
    // Register to Factory
    `uvm_component_utils(adder_test)
    
    // Properties
    adder_env e;
    
    // Constructor
    function new(string path = "test", uvm_component parent = null);
        super.new(path, parent);
    endfunction
    
    // Build Phase
    virtual function void build_phase(uvm_phase phase);
        super.build_phase(phase);
        e = adder_env::type_id::create("env", this);
    endfunction
endclass

////////////////////////////////////////////////////////////////////////////////// TOP TB

module section5_lastvideo;
    adder_if aif();     // these parenthesises () are the must when create an instance of interface even when interface has no parameter
    int tmptoshowwaveform = 0;
    
    adder dut(
        .a(aif.a), 
        .b(aif.b), 
        .y(aif.y)
        );
        
    initial begin
        uvm_config_db#(virtual adder_if)::set(null, "uvm_test_top.env.agent.drv", "aif", aif);
        run_test("adder_test");
    end
endmodule
