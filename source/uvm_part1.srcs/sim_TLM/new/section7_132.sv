`include "uvm_macros.svh"
import uvm_pkg::*;

//////////////////////////////////////////////////////////////////////////////////

class l132_producer extends uvm_component;
    // Register to Factory
    `uvm_component_utils(l132_producer)

    // Properties
    int data = 12;         

    // Transport port
    uvm_analysis_port #(int) port;

    // Constructor
    function new(string path = "l132_producer", uvm_component parent = null);
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
            `uvm_info("PROD", $sformatf("Data Broadcasted: %0d", data), UVM_NONE);
            port.write(data);
        phase.drop_objection(this);
    endtask
endclass

//////////////////////////////////////////////////////////////////////////////////

class l132_consumer1 extends uvm_component;
    // Register to Factory
    `uvm_component_utils(l132_consumer1)

    // Transport port
    uvm_analysis_imp #(int, l132_consumer1) imp;

    // Constructor
    function new(string path = "l132_consumer1", uvm_component parent = null);
        super.new(path, parent);
    endfunction

    // Build Phase;
    virtual function void build_phase(uvm_phase phase);
        super.build_phase(phase);
        imp = new("imp", this);
    endfunction
    
    // Write Method
    virtual function void write(int datar);
        `uvm_info("CONS1", $sformatf("Data Recv: %0d", datar), UVM_NONE);
    endfunction
endclass

//////////////////////////////////////////////////////////////////////////////////

class l132_consumer2 extends uvm_component;
    // Register to Factory
    `uvm_component_utils(l132_consumer2)

    // Transport port
    uvm_analysis_imp #(int, l132_consumer2) imp;

    // Constructor
    function new(string path = "l132_consumer2", uvm_component parent = null);
        super.new(path, parent);
    endfunction

    // Build Phase;
    virtual function void build_phase(uvm_phase phase);
        super.build_phase(phase);
        imp = new("imp", this);
    endfunction
    
    // Write Method
    virtual function void write(int datar);
        `uvm_info("CONS2", $sformatf("Data Recv: %0d", datar), UVM_NONE);
    endfunction
endclass

//////////////////////////////////////////////////////////////////////////////////

class l132_env extends uvm_env;
    // Register to Factory
    `uvm_component_utils(l132_env)
    
    // Properties
    l132_producer  p;
    l132_consumer1 c1;
    l132_consumer2 c2;
    
    // Constructor
    function new(string path = "l132_env", uvm_component parent = null);
        super.new(path, parent);
    endfunction

    // Build Phase
    virtual function void build_phase(uvm_phase phase);
        super.build_phase(phase);
        p = l132_producer::type_id::create("p", this);
        c1 = l132_consumer1::type_id::create("c1", this);
        c2 = l132_consumer2::type_id::create("c2", this);
    endfunction
    
    // Connect Phase
    virtual function void connect_phase(uvm_phase phase);
        super.connect_phase(phase);
        p.port.connect(c1.imp);
        p.port.connect(c2.imp);
    endfunction
endclass

//////////////////////////////////////////////////////////////////////////////////

class l132_test extends uvm_test;
    // Register to Factory
    `uvm_component_utils(l132_test)
    
    // Properties
    l132_env e;
    
    // Constructor
    function new(string path = "l132_test", uvm_component parent = null);
        super.new(path, parent);
    endfunction

    // Build Phase
    virtual function void build_phase(uvm_phase phase);
        super.build_phase(phase);
        e = l132_env::type_id::create("e", this);
    endfunction
endclass

//////////////////////////////////////////////////////////////////////////////////

module section7_132;
    initial begin
        run_test("l132_test");
    end
endmodule

