`include "uvm_macros.svh"
import uvm_pkg::*;

//////////////////////////////////////////////////////////////////////////////////

class l151_transaction extends uvm_sequence_item;
    // Properties
    rand bit [3:0] a;
    rand bit [3:0] b;
         bit [4:0] y;
    
    // Constructor
    function new(string inst = "l151_transaction");
        super.new(inst);
    endfunction

    // Field Macros
    `uvm_object_utils_begin(l151_transaction);
        `uvm_field_int(a, UVM_DEFAULT);
        `uvm_field_int(b, UVM_DEFAULT);
        `uvm_field_int(y, UVM_DEFAULT);
    `uvm_object_utils_end;
endclass

//////////////////////////////////////////////////////////////////////////////////

class l151_sequence1 extends uvm_sequence#(l151_transaction);
    // Register to Factory
    `uvm_object_utils(l151_sequence1)
    
    // Properties
    l151_transaction trans;
    
    // Constructor
    function new(string inst = "seq1");
        super.new(inst);
    endfunction

    // Body Task
    virtual task body();
        repeat(3) begin
            trans = l151_transaction::type_id::create("trans");
            `uvm_info("SEQ_1", "SEQ started", UVM_NONE);
            start_item(trans);
            trans.randomize();
            finish_item(trans);
            `uvm_info("SEQ_1", "SEQ Ended", UVM_NONE);
        end
    endtask
endclass

//////////////////////////////////////////////////////////////////////////////////

class l151_sequence2 extends uvm_sequence#(l151_transaction);
    // Register to Factory
    `uvm_object_utils(l151_sequence2)
    
    // Properties
    l151_transaction trans;
    
    // Constructor
    function new(string inst = "seq2");
        super.new(inst);
    endfunction

    // Body Task
    virtual task body();
        repeat(3) begin
            trans = l151_transaction::type_id::create("trans");
            `uvm_info("SEQ_2", "SEQ started", UVM_NONE);
            start_item(trans);
            trans.randomize();
            finish_item(trans);
            `uvm_info("SEQ_2", "SEQ Ended", UVM_NONE);
        end
    endtask
endclass

//////////////////////////////////////////////////////////////////////////////////

class l151_driver extends uvm_driver#(l151_transaction);
    // Register to Factory
    `uvm_component_utils(l151_driver);      
    
    // Properties
    l151_transaction t;         // data container
    
    // Constructor
    function new(string path = "DRV", uvm_component parent = null);
        super.new(path, parent);
    endfunction
    
    // Build Phase
    virtual function void build_phase(uvm_phase phase);
        super.build_phase(phase);
        t = l151_transaction::type_id::create("t");
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

class l151_agent extends uvm_agent;
    // Register to Factory
    `uvm_component_utils(l151_agent);
    
    // Properties
    l151_driver d;
    uvm_sequencer #(l151_transaction) seqr;
    
    // Constructor
    function new(string path = "AGENT", uvm_component parent = null);
        super.new(path, parent);
    endfunction
    
    // Build Phase
    virtual function void build_phase(uvm_phase phase);
        super.build_phase(phase);
        d = l151_driver::type_id::create("d", this);
        seqr = uvm_sequencer#(l151_transaction)::type_id::create("seqr", this);
    endfunction
    
    // Connect Phase
    virtual function void connect_phase(uvm_phase phase);
        super.connect_phase(phase);
        d.seq_item_port.connect(seqr.seq_item_export);
    endfunction
endclass

//////////////////////////////////////////////////////////////////////////////////

class l151_env extends uvm_env;
    // Register to Factory
    `uvm_component_utils(l151_env);
    
    // Properties
    l151_agent a;
    
    // Constructor
    function new(string path = "ENV", uvm_component parent = null);
        super.new(path, parent);
    endfunction
    
    // Build Phase
    virtual function void build_phase(uvm_phase phase);
        super.build_phase(phase);
        a = l151_agent::type_id::create("a", this);
    endfunction
endclass

//////////////////////////////////////////////////////////////////////////////////

class l151_test extends uvm_test;
    // Register to Factory
    `uvm_component_utils(l151_test);
    
    // Properties
    l151_env e;
    l151_sequence1 s1;
    l151_sequence2 s2;
    
    // Constructor
    function new(string path = "TEST", uvm_component parent = null);
        super.new(path, parent);
    endfunction
    
    // Build Phase
    virtual function void build_phase(uvm_phase phase);
        super.build_phase(phase);
        e  = l151_env::type_id::create("e", this);
        s1 = l151_sequence1::type_id::create("s1");
        s2 = l151_sequence2::type_id::create("s2");
    endfunction
    
    // Run Phase
    virtual task run_phase(uvm_phase phase);
        phase.raise_objection(this);
            this.e.a.seqr.set_arbitration(UVM_SEQ_ARB_STRICT_FIFO);
            fork
                s1.start(this.e.a.seqr, null, 100);
                s2.start(this.e.a.seqr, null, 200);
            join
        phase.drop_objection(this);
    endtask
endclass

//////////////////////////////////////////////////////////////////////////////////

module section8_151;
    initial begin
        run_test("l151_test");
    end
endmodule

