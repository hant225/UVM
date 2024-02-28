`timescale 1ns / 1ps
`include "uvm_macros.svh"
import uvm_pkg::*;
//////////////////////////////////////////////////////////////////////////////////

class env extends uvm_env;
    // Register to Factory
    `uvm_component_utils(env)
    
    // Properties
    int data;
    
    // Constructor
    function new(string path = "env", uvm_component parent);
        super.new(path, parent);
    endfunction
    
    // Build Phase
    virtual function void build_phase(uvm_phase phase);
        super.build_phase(phase);
        
        if(uvm_config_db#(int)::get(null, "uvm_test_top", "data", data))    // last argument data is the variable to store the data if get successfully
            `uvm_info("ENV", $sformatf("Value of data : %0d", data), UVM_NONE)
        else
            `uvm_error("ENV", "Unable to access the value")
    endfunction
endclass

//////////////////////////////////////////////////////////////////////////////////

class test extends uvm_test;
    // Register to Factory
    `uvm_component_utils(test)
    
    // Properties
    env e;
    
    // Constructor
    function new(string path = "test", uvm_component parent);
        super.new(path, parent);
    endfunction
    
    // Build Phase
    virtual function void build_phase(uvm_phase phase);
        super.build_phase(phase);
        e = env::type_id::create("e", this);
        // Config DB
        uvm_config_db#(int)::set(null, "uvm_test_top", "data", 12);       // context + instance name + key + value
    endfunction
endclass

//////////////////////////////////////////////////////////////////////////////////
module section5_77;
    initial begin
        run_test("test");
    end
endmodule
