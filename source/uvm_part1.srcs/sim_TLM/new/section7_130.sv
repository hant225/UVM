`include "uvm_macros.svh"
import uvm_pkg::*;

//////////////////////////////////////////////////////////////////////////////////

class l130_producer extends uvm_component;
    // Register to Factory
    `uvm_component_utils(l130_producer)

    // Properties
    int datas = 12;         // data that send
    int datak = 0;          // data that received

    // Transport port
    uvm_blocking_transport_port #(int, int) port;

    // Constructor
    function new(string path = "l130_producer", uvm_component parent = null);
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
            port.transport(datas, datak);
            `uvm_info("PROD", $sformatf("Data send: %0d, Data Recv: %0d", datas, datak), UVM_NONE);
        phase.drop_objection(this);
    endtask
endclass

//////////////////////////////////////////////////////////////////////////////////

class l130_consumer extends uvm_component;
    // Register to Factory
    `uvm_component_utils(l130_consumer)

    // Properties
    int datas = 13;
    int datar = 0;

    // Transport port
    uvm_blocking_transport_imp #(int, int, l130_consumer) imp;

    // Constructor
    function new(string path = "l130_consumer", uvm_component parent = null);
        super.new(path, parent);
    endfunction

    // Build Phase;
    virtual function void build_phase(uvm_phase phase);
        super.build_phase(phase);
        imp = new("imp", this);
    endfunction
    
    // Transport Method
    virtual task transport(input int datar, output int datas);
        datas = this.datas;
        `uvm_info("CONS", $sformatf("Data Sent: %0d, Data Recv: %0d", datas, datar), UVM_NONE)
    endtask
endclass

class l130_env extends uvm_env;
    // Register to Factory
    `uvm_component_utils(l130_env)
    
    // Properties
    l130_producer p;
    l130_consumer c;
    
    // Constructor
    function new(string path = "l130_env", uvm_component parent = null);
        super.new(path, parent);
    endfunction

    // Build Phase
    virtual function void build_phase(uvm_phase phase);
        super.build_phase(phase);
        p = l130_producer::type_id::create("p", this);
        c = l130_consumer::type_id::create("c", this);
    endfunction
    
    // Connect Phase
    virtual function void connect_phase(uvm_phase phase);
        super.connect_phase(phase);
        p.port.connect(c.imp);
    endfunction
endclass

//////////////////////////////////////////////////////////////////////////////////

class l130_test extends uvm_test;
    // Register to Factory
    `uvm_component_utils(l130_test)
    
    // Properties
    l130_env e;
    
    // Constructor
    function new(string path = "l130_test", uvm_component parent = null);
        super.new(path, parent);
    endfunction

    // Build Phase
    virtual function void build_phase(uvm_phase phase);
        super.build_phase(phase);
        e = l130_env::type_id::create("e", this);
    endfunction
endclass

//////////////////////////////////////////////////////////////////////////////////

module section7_130;
    initial begin
        run_test("l130_test");
    end
endmodule

