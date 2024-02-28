`include "uvm_macros.svh"
import uvm_pkg::*;

//////////////////////////////////////////////////////////////////////////////////

class transaction extends uvm_sequence_item;
    // Properties
    rand bit [3:0] a;
    rand bit [3:0] b;
         bit [4:0] y;

    // Constructor
    function new(string inst = "transaction");
        super.new(inst);
    endfunction

    // Field Macros
    `uvm_object_utils_begin(transaction);
        `uvm_field_int(a, UVM_DEFAULT);
        `uvm_field_int(b, UVM_DEFAULT);
        `uvm_field_int(y, UVM_DEFAULT);
    `uvm_object_utils_end
endclass

//////////////////////////////////////////////////////////////////////////////////

class sequence1 extends uvm_sequence#(transaction);
    // Register to Factory
    `uvm_object_utils(sequence1)

    // Constructor
    function new(string inst = "sequence1");
        super.new(inst);
    endfunction

    // Pre Body
    virtual task pre_body();
        `uvm_info("SEQ1", "PRE-BODY EXECUTED", UVM_NONE);
    endtask
    
    // Body
    virtual task body();
        `uvm_info("SEQ1", "BODY EXECUTED", UVM_NONE);
    endtask
    
    // Post Body
    virtual task post_body();
        `uvm_info("SEQ1", "POST-BODY EXECUTED", UVM_NONE);
    endtask
endclass

//////////////////////////////////////////////////////////////////////////////////

class driver extends uvm_driver#(transaction);
    // Register to Factory
    `uvm_component_utils(driver);
    
    // Properties
    transaction t;
    
    // Constructor
    function new(string path = "DRV", uvm_component parent = null);
        super.new(path, parent);
    endfunction
    
    // Build Phase
    virtual function void build_phase(uvm_phase phase);
        super.build_phase(phase);
        t = transaction::type_id::create("t");
    endfunction
    
    // Run Phase
    virtual task run_phase(uvm_phase phase);
        forever begin
            seq_item_port.get_next_item(t);
            /* Apply Stimulus to DUT here */
            seq_item_port.item_done();
        end
    endtask
endclass

//////////////////////////////////////////////////////////////////////////////////

class agent extends uvm_agent;
    // Register to Factory
    `uvm_component_utils(agent);
    
    // Properties
    driver d;
    uvm_sequencer #(transaction) seqr;
    
    // Constructor
    function new(string path = "AGENT", uvm_component parent = null);
        super.new(path, parent);
    endfunction
    
    // Build Phase
    virtual function void build_phase(uvm_phase phase);
        super.build_phase(phase);
        d = driver::type_id::create("d", this);
        seqr = uvm_sequencer#(transaction)::type_id::create("seqr", this);
    endfunction
    
    // Connect Phase
    virtual function void connect_phase(uvm_phase phase);
        super.connect_phase(phase);
        d.seq_item_port.connect(seqr.seq_item_export);
    endfunction
endclass

//////////////////////////////////////////////////////////////////////////////////

class env extends uvm_env;
    // Register to Factory
    `uvm_component_utils(env);
    
    // Properties
    agent a;
    
    // Constructor
    function new(string path = "ENV", uvm_component parent = null);
        super.new(path, parent);
    endfunction
    
    // Build Phase
    virtual function void build_phase(uvm_phase phase);
        super.build_phase(phase);
        a = agent::type_id::create("a", this);
    endfunction
endclass

//////////////////////////////////////////////////////////////////////////////////

class test extends uvm_test;
    // Register to Factory
    `uvm_component_utils(test);
    
    // Properties
    env e;
    sequence1 seq1;
    
    // Constructor
    function new(string path = "TEST", uvm_component parent = null);
        super.new(path, parent);
    endfunction
    
    // Build Phase
    virtual function void build_phase(uvm_phase phase);
        super.build_phase(phase);
        e = env::type_id::create("e", this);
        seq1 = sequence1::type_id::create("seq1");
    endfunction
    
    // Run Phase
    virtual task run_phase(uvm_phase phase);
        phase.raise_objection(this);
            seq1.start(this.e.a.seqr);
        phase.drop_objection(this);
    endtask
endclass

//////////////////////////////////////////////////////////////////////////////////

module section8_136;
    initial begin
        run_test("test");
    end
endmodule

