`include "uvm_macros.svh"
import uvm_pkg::*;

//////////////////////////////////////////////////////////////////////////////////

class l122_producer extends uvm_component;
    // Register to Factory
    `uvm_component_utils(l122_producer)

    // Properties
    int data = 12;
    
    // Put Port
    uvm_blocking_put_port #(int) send;

    // Constructor
    function new(string path = "l122_producer", uvm_component parent = null);
        super.new(path, parent);
    endfunction

    // Build Phase;
    virtual function void build_phase(uvm_phase phase);
        super.build_phase(phase);
        send = new("send", this);
    endfunction
    
    // Main Phase
    task main_phase(uvm_phase phase);
        phase.raise_objection(this);
        `uvm_info("PROD", $sformatf("Data Sent : %0d", data), UVM_NONE);
        send.put(data);
        phase.drop_objection(this);
    endtask
endclass

//////////////////////////////////////////////////////////////////////////////////

class l122_consumer extends uvm_component;
    // Register to Factory
    `uvm_component_utils(l122_consumer)

    // Properties
    int data;
    
    // Put Export
    uvm_blocking_put_imp #(int, l122_consumer) imp;

    // Constructor
    function new(string path = "l122_consumer", uvm_component parent = null);
        super.new(path, parent);
    endfunction

    // Build Phase;
    virtual function void build_phase(uvm_phase phase);
        super.build_phase(phase);
        imp = new("imp", this);
    endfunction
    
    // Put Method
    function void put(int datar);
        `uvm_info("CONS", $sformatf("Data Rcvd : %0d", datar), UVM_NONE);
    endfunction
endclass

//////////////////////////////////////////////////////////////////////////////////

class l122_env extends uvm_env;
    // Register to Factory
    `uvm_component_utils(l122_env)
    
    // Properties
    l122_producer p;
    l122_consumer c;
    
    // Constructor
    function new(string path = "l122_env", uvm_component parent = null);
        super.new(path, parent);
    endfunction

    // Build Phase
    virtual function void build_phase(uvm_phase phase);
        super.build_phase(phase);
        p = l122_producer::type_id::create("p", this);
        c = l122_consumer::type_id::create("c", this);
    endfunction
    
    // Connect Phase
    virtual function void connect_phase(uvm_phase phase);
        super.connect_phase(phase);
        p.send.connect(c.imp);
    endfunction
endclass

//////////////////////////////////////////////////////////////////////////////////

class l122_test extends uvm_test;
    // Register to Factory
    `uvm_component_utils(l122_test)
    
    // Properties
    l122_env e;
    
    // Constructor
    function new(string path = "l122_test", uvm_component parent = null);
        super.new(path, parent);
    endfunction

    // Build Phase
    virtual function void build_phase(uvm_phase phase);
        super.build_phase(phase);
        e = l122_env::type_id::create("e", this);
    endfunction
endclass

//////////////////////////////////////////////////////////////////////////////////

module section7_122;
    initial begin
        run_test("l122_test");
    end
endmodule

