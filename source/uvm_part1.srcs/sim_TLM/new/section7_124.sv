`include "uvm_macros.svh"
import uvm_pkg::*;

//////////////////////////////////////////////////////////////////////////////////

class l124_subproducer extends uvm_component;
    // Register to Factory
    `uvm_component_utils(l124_subproducer)

    // Properties
    int data = 12;
    
    // Put Port
    uvm_blocking_put_port #(int) subport;

    // Constructor
    function new(string path = "l124_subproducer", uvm_component parent = null);
        super.new(path, parent);
    endfunction

    // Build Phase;
    virtual function void build_phase(uvm_phase phase);
        super.build_phase(phase);
        subport = new("subport", this);
    endfunction
    
    // Main Phase
    task main_phase(uvm_phase phase);
        phase.raise_objection(this);
        `uvm_info("SUBPROD", $sformatf("Data Sent : %0d", data), UVM_NONE);
        subport.put(data);
        phase.drop_objection(this);
    endtask
endclass

//////////////////////////////////////////////////////////////////////////////////

class l124_producer extends uvm_component;
    // Register to Factory
    `uvm_component_utils(l124_producer)

    // Properties
    l124_subproducer s;
    
    // Put Port
    uvm_blocking_put_port #(int) port;

    // Constructor
    function new(string path = "l124_producer", uvm_component parent = null);
        super.new(path, parent);
    endfunction

    // Build Phase;
    virtual function void build_phase(uvm_phase phase);
        super.build_phase(phase);        
        port = new("port", this);
        s = l124_subproducer::type_id::create("s", this);
    endfunction
    
    // Connect Phase
    virtual function void connect_phase(uvm_phase phase);
        super.connect_phase(phase);
        s.subport.connect(this.port);                // connect subport to port
    endfunction
    
endclass

//////////////////////////////////////////////////////////////////////////////////

class l124_consumer extends uvm_component;
    // Register to Factory
    `uvm_component_utils(l124_consumer)

    // Properties
    int data;
    
    // Put Export
    uvm_blocking_put_imp #(int, l124_consumer) imp;

    // Constructor
    function new(string path = "l124_consumer", uvm_component parent = null);
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

class l124_env extends uvm_env;
    // Register to Factory
    `uvm_component_utils(l124_env)
    
    // Properties
    l124_producer p;
    l124_consumer c;
    
    // Constructor
    function new(string path = "l124_env", uvm_component parent = null);
        super.new(path, parent);
    endfunction

    // Build Phase
    virtual function void build_phase(uvm_phase phase);
        super.build_phase(phase);
        p = l124_producer::type_id::create("p", this);
        c = l124_consumer::type_id::create("c", this);
    endfunction
    
    // Connect Phase
    virtual function void connect_phase(uvm_phase phase);
        super.connect_phase(phase);
        p.port.connect(c.imp);
    endfunction
endclass

//////////////////////////////////////////////////////////////////////////////////

class l124_test extends uvm_test;
    // Register to Factory
    `uvm_component_utils(l124_test)
    
    // Properties
    l124_env e;
    
    // Constructor
    function new(string path = "l124_test", uvm_component parent = null);
        super.new(path, parent);
    endfunction

    // Build Phase
    virtual function void build_phase(uvm_phase phase);
        super.build_phase(phase);
        e = l124_env::type_id::create("e", this);
    endfunction
    
    // EoE Phase
    virtual function void end_of_elaboration_phase(uvm_phase phase);
        super.end_of_elaboration_phase(phase);
        uvm_top.print_topology();           // print entire heirarchy
    endfunction
endclass

//////////////////////////////////////////////////////////////////////////////////

module section7_124;
    initial begin
        run_test("l124_test");
    end
endmodule

