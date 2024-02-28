`include "uvm_macros.svh"
import uvm_pkg::*;

//////////////////////////////////////////////////////////////////////////////////

class l155_transaction extends uvm_sequence_item;
    // Properties
    rand bit [3:0] a;
    rand bit [3:0] b;
         bit [4:0] y;
    
    // Constructor
    function new(string inst = "l155_transaction");
        super.new(inst);
    endfunction

    // Field Macros
    `uvm_object_utils_begin(l155_transaction);
        `uvm_field_int(a, UVM_DEFAULT);
        `uvm_field_int(b, UVM_DEFAULT);
        `uvm_field_int(y, UVM_DEFAULT);
    `uvm_object_utils_end;
endclass

//////////////////////////////////////////////////////////////////////////////////

class l155_sequence1 extends uvm_sequence#(l155_transaction);
    // Register to Factory
    `uvm_object_utils(l155_sequence1)
    
    // Properties
    l155_transaction trans;
    
    // Constructor
    function new(string inst = "seq1");
        super.new(inst);
    endfunction

    // Body Task
    virtual task body();
        lock(m_sequencer);
            repeat(3) begin
                trans = l155_transaction::type_id::create("trans");
                `uvm_info("SEQ_1", "SEQ started", UVM_NONE);
                start_item(trans);
                trans.randomize();
                finish_item(trans);
                `uvm_info("SEQ_1", "SEQ Ended", UVM_NONE);
            end
        unlock(m_sequencer);
    endtask
endclass

//////////////////////////////////////////////////////////////////////////////////

class l155_sequence2 extends uvm_sequence#(l155_transaction);
    // Register to Factory
    `uvm_object_utils(l155_sequence2)
    
    // Properties
    l155_transaction trans;
    
    // Constructor
    function new(string inst = "seq2");
        super.new(inst);
    endfunction

    // Body Task
    virtual task body();
        grab(m_sequencer);    
            repeat(3) begin
                trans = l155_transaction::type_id::create("trans");
                `uvm_info("SEQ_2", "SEQ started", UVM_NONE);
                start_item(trans);
                trans.randomize();
                finish_item(trans);
                `uvm_info("SEQ_2", "SEQ Ended", UVM_NONE);
            end
        ungrab(m_sequencer);
    endtask
endclass

//////////////////////////////////////////////////////////////////////////////////

class l155_driver extends uvm_driver#(l155_transaction);
    // Register to Factory
    `uvm_component_utils(l155_driver);      
    
    // Properties
    l155_transaction t;         // data container
    
    // Constructor
    function new(string path = "DRV", uvm_component parent = null);
        super.new(path, parent);
    endfunction
    
    // Build Phase
    virtual function void build_phase(uvm_phase phase);
        super.build_phase(phase);
        t = l155_transaction::type_id::create("t");
    endfunction
    
    // Run Phase
    virtual task run_phase(uvm_phase phase);
        forever begin
            seq_item_port.get_next_item(t);
            seq_item_port.item_done();
        end
    endtask
endclass

//////////////////////////////////////////////////////////////////////////////////

class l155_agent extends uvm_agent;
    // Register to Factory
    `uvm_component_utils(l155_agent);
    
    // Properties
    l155_driver d;
    uvm_sequencer #(l155_transaction) seqr;
    
    // Constructor
    function new(string path = "AGENT", uvm_component parent = null);
        super.new(path, parent);
    endfunction
    
    // Build Phase
    virtual function void build_phase(uvm_phase phase);
        super.build_phase(phase);
        d = l155_driver::type_id::create("d", this);
        seqr = uvm_sequencer#(l155_transaction)::type_id::create("seqr", this);
    endfunction
    
    // Connect Phase
    virtual function void connect_phase(uvm_phase phase);
        super.connect_phase(phase);
        d.seq_item_port.connect(seqr.seq_item_export);
    endfunction
endclass

//////////////////////////////////////////////////////////////////////////////////

class l155_env extends uvm_env;
    // Register to Factory
    `uvm_component_utils(l155_env);
    
    // Properties
    l155_agent a;
    
    // Constructor
    function new(string path = "ENV", uvm_component parent = null);
        super.new(path, parent);
    endfunction
    
    // Build Phase
    virtual function void build_phase(uvm_phase phase);
        super.build_phase(phase);
        a = l155_agent::type_id::create("a", this);
    endfunction
endclass

//////////////////////////////////////////////////////////////////////////////////

class l155_test extends uvm_test;
    // Register to Factory
    `uvm_component_utils(l155_test);
    
    // Properties
    l155_env e;
    l155_sequence1 s1;
    l155_sequence2 s2;
    
    // Constructor
    function new(string path = "TEST", uvm_component parent = null);
        super.new(path, parent);
    endfunction
    
    // Build Phase
    virtual function void build_phase(uvm_phase phase);
        super.build_phase(phase);
        e  = l155_env::type_id::create("e", this);
        s1 = l155_sequence1::type_id::create("s1");
        s2 = l155_sequence2::type_id::create("s2");
    endfunction
    
    // Run Phase
    virtual task run_phase(uvm_phase phase);
        phase.raise_objection(this);
            
            fork
                s1.start(this.e.a.seqr, null, 100);
                s2.start(this.e.a.seqr, null, 200);
            join
        phase.drop_objection(this);
    endtask
endclass

//////////////////////////////////////////////////////////////////////////////////

module section8_155;
    initial begin
        run_test("l155_test");
    end
endmodule

