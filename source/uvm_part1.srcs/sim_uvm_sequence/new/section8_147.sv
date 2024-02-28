`include "uvm_macros.svh"
import uvm_pkg::*;

//////////////////////////////////////////////////////////////////////////////////

/*
SEQ_ARB_FIFO (DEFAULT): first in first out .. priority won't work -- priority do not effect
SEQ_ARB_WEIGHTED: weight is used for priority 
SEQ_ARB_RANDOM: pure random - priority does not effect
SEQ_ARB_STRICT_FIFO: support priority - which has high prior will strictly go 1st, if weight are
                                        equal then which come first will be call first
SEQ_ARB_STRICT_RANDOM: support priority - which has high prior will strictly go 1st, if weight are
                                          equal then which seq come will decided by randomization
SEQ_ARB_USER:
*/

//////////////////////////////////////////////////////////////////////////////////

class l147_transaction extends uvm_sequence_item;
    // Properties
    rand bit [3:0] a;
    rand bit [3:0] b;
         bit [4:0] y;
    
    // Constructor
    function new(string inst = "l147_transaction");
        super.new(inst);
    endfunction

    // Field Macros
    `uvm_object_utils_begin(l147_transaction);
        `uvm_field_int(a, UVM_DEFAULT);
        `uvm_field_int(b, UVM_DEFAULT);
        `uvm_field_int(y, UVM_DEFAULT);
    `uvm_object_utils_end;
endclass

//////////////////////////////////////////////////////////////////////////////////

class l147_sequence1 extends uvm_sequence#(l147_transaction);
    // Register to Factory
    `uvm_object_utils(l147_sequence1)
    
    // Properties
    l147_transaction trans;
    
    // Constructor
    function new(string inst = "seq1");
        super.new(inst);
    endfunction

    // Body Task
    virtual task body();
        trans = l147_transaction::type_id::create("trans");
        `uvm_info("SEQ_1", "SEQ started", UVM_NONE);
        start_item(trans);
        trans.randomize();
        finish_item(trans);
        `uvm_info("SEQ_1", "SEQ Ended", UVM_NONE);
    endtask
endclass

//////////////////////////////////////////////////////////////////////////////////

class l147_sequence2 extends uvm_sequence#(l147_transaction);
    // Register to Factory
    `uvm_object_utils(l147_sequence2)
    
    // Properties
    l147_transaction trans;
    
    // Constructor
    function new(string inst = "seq2");
        super.new(inst);
    endfunction

    // Body Task
    virtual task body();
        trans = l147_transaction::type_id::create("trans");
        `uvm_info("SEQ_2", "SEQ started", UVM_NONE);
        start_item(trans);
        trans.randomize();
        finish_item(trans);
        `uvm_info("SEQ_2", "SEQ Ended", UVM_NONE);
    endtask
endclass

//////////////////////////////////////////////////////////////////////////////////

class l147_driver extends uvm_driver#(l147_transaction);
    // Register to Factory
    `uvm_component_utils(l147_driver);      
    
    // Properties
    l147_transaction t;         // data container
    
    // Constructor
    function new(string path = "DRV", uvm_component parent = null);
        super.new(path, parent);
    endfunction
    
    // Build Phase
    virtual function void build_phase(uvm_phase phase);
        super.build_phase(phase);
        t = l147_transaction::type_id::create("t");
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

class l147_agent extends uvm_agent;
    // Register to Factory
    `uvm_component_utils(l147_agent);
    
    // Properties
    l147_driver d;
    uvm_sequencer #(l147_transaction) seqr;
    
    // Constructor
    function new(string path = "AGENT", uvm_component parent = null);
        super.new(path, parent);
    endfunction
    
    // Build Phase
    virtual function void build_phase(uvm_phase phase);
        super.build_phase(phase);
        d = l147_driver::type_id::create("d", this);
        seqr = uvm_sequencer#(l147_transaction)::type_id::create("seqr", this);
    endfunction
    
    // Connect Phase
    virtual function void connect_phase(uvm_phase phase);
        super.connect_phase(phase);
        d.seq_item_port.connect(seqr.seq_item_export);
    endfunction
endclass

//////////////////////////////////////////////////////////////////////////////////

class l147_env extends uvm_env;
    // Register to Factory
    `uvm_component_utils(l147_env);
    
    // Properties
    l147_agent a;
    
    // Constructor
    function new(string path = "ENV", uvm_component parent = null);
        super.new(path, parent);
    endfunction
    
    // Build Phase
    virtual function void build_phase(uvm_phase phase);
        super.build_phase(phase);
        a    = l147_agent::type_id::create("a", this);
    endfunction
endclass

//////////////////////////////////////////////////////////////////////////////////

class l147_test extends uvm_test;
    // Register to Factory
    `uvm_component_utils(l147_test);
    
    // Properties
    l147_env e;
    l147_sequence1 s1;
    l147_sequence2 s2;
    
    // Constructor
    function new(string path = "TEST", uvm_component parent = null);
        super.new(path, parent);
    endfunction
    
    // Build Phase
    virtual function void build_phase(uvm_phase phase);
        super.build_phase(phase);
        e  = l147_env::type_id::create("e", this);
        s1 = l147_sequence1::type_id::create("s1");
        s2 = l147_sequence2::type_id::create("s2");
    endfunction
    
    // Run Phase
    virtual task run_phase(uvm_phase phase);
        phase.raise_objection(this);
            // this.e.a.seqr.set_arbitration(UVM_SEQ_ARB_WEIGHTED);
            // this.e.a.seqr.set_arbitration(UVM_SEQ_ARB_RANDOM);
            // this.e.a.seqr.set_arbitration(UVM_SEQ_ARB_STRICT_FIFO);
            this.e.a.seqr.set_arbitration(UVM_SEQ_ARB_STRICT_RANDOM);
            fork
                // sequence.start(sequencer, parent sequence, priority, call pre_post)
                repeat(5) s1.start(this.e.a.seqr, null, 200);     
                repeat(5) s2.start(this.e.a.seqr, null, 100);
            join
        phase.drop_objection(this);
    endtask
endclass

//////////////////////////////////////////////////////////////////////////////////

module section8_147;
    initial begin
        run_test("l147_test");
    end
endmodule

