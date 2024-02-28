`include "uvm_macros.svh"
import uvm_pkg::*;

//////////////////////////////////////////////////////////////////////////////////

class l128_producer extends uvm_component;
    // Register to Factory
    `uvm_component_utils(l128_producer)

    // Properties
    int data;           // container to store data after get()

    // Get Port
    uvm_blocking_get_port #(int) port;

    // Constructor
    function new(string path = "l128_producer", uvm_component parent = null);
        super.new(path, parent);
    endfunction

    // Build Phase;
    virtual function void build_phase(uvm_phase phase);
        super.build_phase(phase);
        port = new("port", this);
    endfunction
    
    // Main Phase
    task main_phase(uvm_phase phase);
        phase.raise_objection(this);
        port.get(data);
        `uvm_info("PROD", $sformatf("Data Recv : %0d", data), UVM_NONE);
        phase.drop_objection(this);
    endtask
endclass

//////////////////////////////////////////////////////////////////////////////////

class l128_consumer extends uvm_component;
    // Register to Factory
    `uvm_component_utils(l128_consumer)

    // Properties
    int data = 12;           

    // Get Port
    uvm_blocking_get_imp #(int, l128_consumer) imp;

    // Constructor
    function new(string path = "l128_consumer", uvm_component parent = null);
        super.new(path, parent);
    endfunction

    // Build Phase;
    virtual function void build_phase(uvm_phase phase);
        super.build_phase(phase);
        imp = new("imp", this);
    endfunction
    
    // Get Method
    virtual task get(output int datar);             // direction is output in get method
        `uvm_info("CONS", $sformatf("Data Sent : %0d", data), UVM_NONE);
        datar = data;
    endtask
endclass

//////////////////////////////////////////////////////////////////////////////////

class l128_env extends uvm_env;
    // Register to Factory
    `uvm_component_utils(l128_env)

    // Properties
    l128_producer p;
    l128_consumer c;

    // Constructor
    function new(string path = "l128_env", uvm_component parent = null);
        super.new(path, parent);
    endfunction

    // Build Phase;
    virtual function void build_phase(uvm_phase phase);
        super.build_phase(phase);
        p = l128_producer::type_id::create("p", this); 
        c = l128_consumer::type_id::create("c", this);
    endfunction
    
    // Connect Phase
    virtual function void connect_phase(uvm_phase phase);
        super.connect_phase(phase);
        p.port.connect(c.imp);
    endfunction
endclass

//////////////////////////////////////////////////////////////////////////////////

class l128_test extends uvm_test;
    // Register to Factory
    `uvm_component_utils(l128_test)

    // Properties
    l128_env e;

    // Constructor
    function new(string path = "l128_test", uvm_component parent = null);
        super.new(path, parent);
    endfunction

    // Build Phase;
    virtual function void build_phase(uvm_phase phase);
        super.build_phase(phase);
        e = l128_env::type_id::create("e", this); 
    endfunction
endclass

//////////////////////////////////////////////////////////////////////////////////

module section7_128;
    initial begin
        run_test("l128_test");
    end
endmodule

