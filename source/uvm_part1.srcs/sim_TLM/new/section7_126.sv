`include "uvm_macros.svh"
import uvm_pkg::*;

//////////////////////////////////////////////////////////////////////////////////

class l126_producer extends uvm_component;
    // Register to Factory
    `uvm_component_utils(l126_producer)

    // Properties
    int data = 12;
    
    // Put Port
    uvm_blocking_put_port #(int) port;

    // Constructor
    function new(string path = "l126_producer", uvm_component parent = null);
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
        `uvm_info("PROD", $sformatf("Data Send: %0d", data), UVM_NONE)
        port.put(data);
        phase.drop_objection(this);
    endtask   
endclass

//////////////////////////////////////////////////////////////////////////////////

class l126_subconsumer extends uvm_component;
    // Register to Factory
    `uvm_component_utils(l126_subconsumer)
    
    // Put Export
    uvm_blocking_put_imp #(int, l126_subconsumer) imp;

    // Constructor
    function new(string path = "l126_subconsumer", uvm_component parent = null);
        super.new(path, parent);
    endfunction

    // Build Phase;
    virtual function void build_phase(uvm_phase phase);
        super.build_phase(phase);
        imp = new("imp", this);
    endfunction
    
    // Put Method
    function void put(int datar);
        `uvm_info("SUBCONS", $sformatf("Data Rcvd : %0d", datar), UVM_NONE);
    endfunction
endclass

//////////////////////////////////////////////////////////////////////////////////

class l126_consumer extends uvm_component;
    // Register to Factory
    `uvm_component_utils(l126_consumer)
    
    // Properties
    l126_subconsumer s;
    
    // Put Export
    uvm_blocking_put_export #(int) expo;

    // Constructor
    function new(string path = "l126_consumer", uvm_component parent = null);
        super.new(path, parent);
    endfunction

    // Build Phase;
    virtual function void build_phase(uvm_phase phase);
        super.build_phase(phase);
        expo = new("expo", this);
        s = l126_subconsumer::type_id::create("s", this);
    endfunction
    
    // Connect Phase
    virtual function void connect_phase(uvm_phase phase);
        super.connect_phase(phase);
        this.expo.connect(s.imp);
    endfunction
endclass

//////////////////////////////////////////////////////////////////////////////////

class l126_env extends uvm_env;
    // Register to Factory
    `uvm_component_utils(l126_env)
    
    // Properties
    l126_producer p;
    l126_consumer c;
    
    // Constructor
    function new(string path = "l126_env", uvm_component parent = null);
        super.new(path, parent);
    endfunction

    // Build Phase
    virtual function void build_phase(uvm_phase phase);
        super.build_phase(phase);
        p = l126_producer::type_id::create("p", this);
        c = l126_consumer::type_id::create("c", this);
    endfunction
    
    // Connect Phase
    virtual function void connect_phase(uvm_phase phase);
        super.connect_phase(phase);
        p.port.connect(c.expo);
    endfunction
endclass

//////////////////////////////////////////////////////////////////////////////////

class l126_test extends uvm_test;
    // Register to Factory
    `uvm_component_utils(l126_test)
    
    // Properties
    l126_env e;
    
    // Constructor
    function new(string path = "l126_test", uvm_component parent = null);
        super.new(path, parent);
    endfunction

    // Build Phase
    virtual function void build_phase(uvm_phase phase);
        super.build_phase(phase);
        e = l126_env::type_id::create("e", this);
    endfunction
    
    // EoE Phase
    virtual function void end_of_elaboration_phase(uvm_phase phase);
        super.end_of_elaboration_phase(phase);
        uvm_top.print_topology();           // print entire heirarchy
    endfunction
endclass

//////////////////////////////////////////////////////////////////////////////////

module section7_126;
    initial begin
        run_test("l126_test");
    end
endmodule

