`include "uvm_macros.svh"
import uvm_pkg::*;

//////////////////////////////////////////////////////////////////////////////////

class producer extends uvm_component;
    // Register to Factory
    `uvm_component_utils(producer)
    
    // Properties
    int data = 12;
    
    // TLM Port
    uvm_blocking_put_port #(int) send;
    
    // Constructor
    function new(string path = "producer", uvm_component parent = null);
        super.new(path, parent);
        send = new("send", this);
    endfunction
    
    // Main Phase
    task main_phase(uvm_phase phase);
        phase.raise_objection(this);
            send.put(data);                 // put data to TLM export
            `uvm_info("PROD", $sformatf("Data Sent : %0d", data), UVM_NONE);
        phase.drop_objection(this);
    endtask

endclass

//////////////////////////////////////////////////////////////////////////////////

class consumer extends uvm_component;
    // Register to Factory
    `uvm_component_utils(consumer)
    
    // TLM Port
    uvm_blocking_put_export #(int) recv;
    uvm_blocking_put_imp #(int, consumer) imp;
    
    // Constructor
    function new(string path = "consumer", uvm_component parent = null);
        super.new(path, parent);
        recv = new("recv", this);
        imp  = new("imp", this);
    endfunction

    // Put Method
    task put(int datar);        // datar = data received
        `uvm_info("CONS", $sformatf("Data Rcvd : %0d", datar), UVM_NONE);
    endtask
endclass

//////////////////////////////////////////////////////////////////////////////////

class env extends uvm_env;
    // Register to Factory
    `uvm_component_utils(env)
    
    // Properties
    producer p;
    consumer c;
    
    // Constructor
    function new(string path = "env", uvm_component parent = null);
        super.new(path, parent);
    endfunction

    // Build Phase
    virtual function void build_phase(uvm_phase phase);
        super.build_phase(phase);
        p = producer::type_id::create("p", this);
        c = consumer::type_id::create("c", this);
    endfunction
    
    // Connect Phase
    virtual function void connect_phase(uvm_phase phase);
        super.connect_phase(phase);
        p.send.connect(c.recv);
        c.recv.connect(c.imp);
    endfunction
endclass

//////////////////////////////////////////////////////////////////////////////////

class test extends uvm_test;
    // Register to Factory
    `uvm_component_utils(test)
    
    // Properties
    env e;
    
    // Constructor
    function new(string path = "test", uvm_component parent = null);
        super.new(path, parent);
    endfunction

    // Build Phase
    virtual function void build_phase(uvm_phase phase);
        super.build_phase(phase);
        e = env::type_id::create("e", this);
    endfunction
endclass

//////////////////////////////////////////////////////////////////////////////////

module section7_118;
    initial begin
        run_test("test");
    end
endmodule

