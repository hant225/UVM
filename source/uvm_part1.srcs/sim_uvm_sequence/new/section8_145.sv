`include "uvm_macros.svh"
import uvm_pkg::*;

//////////////////////////////////////////////////////////////////////////////////

class l145_transaction extends uvm_sequence_item;
    // Properties
    rand bit [3:0] a;
    rand bit [3:0] b;
         bit [4:0] y;
    
    // Constructor
    function new(string inst = "l145_transaction");
        super.new(inst);
    endfunction

    // Field Macros
    `uvm_object_utils_begin(l145_transaction);
        `uvm_field_int(a, UVM_DEFAULT);
        `uvm_field_int(b, UVM_DEFAULT);
        `uvm_field_int(y, UVM_DEFAULT);
    `uvm_object_utils_end;
endclass

//////////////////////////////////////////////////////////////////////////////////

class l145_sequence1 extends uvm_sequence#(l145_transaction);
    // Register to Factory
    `uvm_object_utils(l145_sequence1)
    
    // Properties
    l145_transaction trans;
    
    // Constructor
    function new(string inst = "seq1");
        super.new(inst);
    endfunction

    // Body Task
    virtual task body();
        trans = l145_transaction::type_id::create("trans");
        `uvm_info("SEQ_1", "SEQ started", UVM_NONE);
        start_item(trans);
        trans.randomize();
        finish_item(trans);
        `uvm_info("SEQ_1", "SEQ Ended", UVM_NONE);
    endtask
endclass

//////////////////////////////////////////////////////////////////////////////////

class l145_sequence2 extends uvm_sequence#(l145_transaction);
    // Register to Factory
    `uvm_object_utils(l145_sequence2)
    
    // Properties
    l145_transaction trans;
    
    // Constructor
    function new(string inst = "seq2");
        super.new(inst);
    endfunction

    // Body Task
    virtual task body();
        trans = l145_transaction::type_id::create("trans");
        `uvm_info("SEQ_2", "SEQ started", UVM_NONE);
        start_item(trans);
        trans.randomize();
        finish_item(trans);
        `uvm_info("SEQ_2", "SEQ Ended", UVM_NONE);
    endtask
endclass

//////////////////////////////////////////////////////////////////////////////////

class l145_driver extends uvm_driver#(l145_transaction);
    // Register to Factory
    `uvm_component_utils(l145_driver);      
    
    // Properties
    l145_transaction trans;         // data container
    
    // Constructor
    function new(string path = "DRV", uvm_component parent = null);
        super.new(path, parent);
    endfunction
    
    // Build Phase
    virtual function void build_phase(uvm_phase phase);
        super.build_phase(phase);
        trans = l145_transaction::type_id::create("trans");
    endfunction
    
    // Run Phase
    virtual task run_phase(uvm_phase phase);
        forever begin
            seq_item_port.get_next_item(trans);
            seq_item_port.item_done();
        end
    endtask
endclass

//////////////////////////////////////////////////////////////////////////////////

class l145_agent extends uvm_agent;
    // Register to Factory
    `uvm_component_utils(l145_agent);
    
    // Properties
    l145_driver d;
    uvm_sequencer #(l145_transaction) seqr;
    
    // Constructor
    function new(string path = "AGENT", uvm_component parent = null);
        super.new(path, parent);
    endfunction
    
    // Build Phase
    virtual function void build_phase(uvm_phase phase);
        super.build_phase(phase);
        d = l145_driver::type_id::create("d", this);
        seqr = uvm_sequencer#(l145_transaction)::type_id::create("seqr", this);
    endfunction
    
    // Connect Phase
    virtual function void connect_phase(uvm_phase phase);
        super.connect_phase(phase);
        d.seq_item_port.connect(seqr.seq_item_export);
    endfunction
endclass

//////////////////////////////////////////////////////////////////////////////////

class l145_env extends uvm_env;
    // Register to Factory
    `uvm_component_utils(l145_env);
    
    // Properties
    l145_agent a;
    
    // Constructor
    function new(string path = "ENV", uvm_component parent = null);
        super.new(path, parent);
    endfunction
    
    // Build Phase
    virtual function void build_phase(uvm_phase phase);
        super.build_phase(phase);
        a    = l145_agent::type_id::create("a", this);
    endfunction
endclass

//////////////////////////////////////////////////////////////////////////////////

class l145_test extends uvm_test;
    // Register to Factory
    `uvm_component_utils(l145_test);
    
    // Properties
    l145_env e;
    l145_sequence1 s1;
    l145_sequence2 s2;
    
    // Constructor
    function new(string path = "TEST", uvm_component parent = null);
        super.new(path, parent);
    endfunction
    
    // Build Phase
    virtual function void build_phase(uvm_phase phase);
        super.build_phase(phase);
        e  = l145_env::type_id::create("e", this);
        s1 = l145_sequence1::type_id::create("s1");
        s2 = l145_sequence2::type_id::create("s2");
    endfunction
    
    // Run Phase
    virtual task run_phase(uvm_phase phase);
        phase.raise_objection(this);
            fork
                s1.start(this.e.a.seqr);
                s2.start(this.e.a.seqr);
            join
        phase.drop_objection(this);
    endtask
endclass

//////////////////////////////////////////////////////////////////////////////////

module section8_145;
    initial begin
        run_test("l145_test");
    end
endmodule

