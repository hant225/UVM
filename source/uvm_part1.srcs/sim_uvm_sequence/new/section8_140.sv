`include "uvm_macros.svh"
import uvm_pkg::*;

//////////////////////////////////////////////////////////////////////////////////

class l140_transaction extends uvm_sequence_item;
    // Properties
    rand bit [3:0] a;
    rand bit [3:0] b;
         bit [4:0] y;
    
    // Constructor
    function new(string inst = "l140_transaction");
        super.new(inst);
    endfunction

    // Field Macros
    `uvm_object_utils_begin(l140_transaction);
        `uvm_field_int(a, UVM_DEFAULT);
        `uvm_field_int(b, UVM_DEFAULT);
        `uvm_field_int(y, UVM_DEFAULT);
    `uvm_object_utils_end;
endclass

//////////////////////////////////////////////////////////////////////////////////

class l140_sequence extends uvm_sequence#(l140_transaction);
    // Register to Factory
    `uvm_object_utils(l140_sequence)
    
    // Properties
    l140_transaction trans;
    
    // Constructor
    function new(string inst = "l140_sequence");
        super.new(inst);
    endfunction

    // Body Task
    virtual task body();
        repeat(5) begin
            `uvm_do(trans);
            `uvm_info("SEQ", $sformatf("a: %0d | b: %0d", trans.a, trans.b), UVM_NONE);
        end
    endtask
endclass

//////////////////////////////////////////////////////////////////////////////////

class l140_driver extends uvm_driver#(l140_transaction);
    // Register to Factory
    `uvm_component_utils(l140_driver);      
    
    // Properties
    l140_transaction trans;         // data container
    
    // Constructor
    function new(string path = "DRV", uvm_component parent = null);
        super.new(path, parent);
    endfunction
    
    // Run Phase
    virtual task run_phase(uvm_phase phase);
        trans = l140_transaction::type_id::create("trans");
        forever begin
            seq_item_port.get_next_item(trans);
            `uvm_info("DRV", $sformatf("a: %0d | b: %0d", trans.a, trans.b), UVM_NONE);
            seq_item_port.item_done();
        end
    endtask
endclass

//////////////////////////////////////////////////////////////////////////////////

class l140_agent extends uvm_agent;
    // Register to Factory
    `uvm_component_utils(l140_agent);
    
    // Properties
    l140_driver d;
    uvm_sequencer #(l140_transaction) seqr;
    
    // Constructor
    function new(string path = "AGENT", uvm_component parent = null);
        super.new(path, parent);
    endfunction
    
    // Build Phase
    virtual function void build_phase(uvm_phase phase);
        super.build_phase(phase);
        d = l140_driver::type_id::create("d", this);
        seqr = uvm_sequencer#(l140_transaction)::type_id::create("seqr", this);
    endfunction
    
    // Connect Phase
    virtual function void connect_phase(uvm_phase phase);
        super.connect_phase(phase);
        d.seq_item_port.connect(seqr.seq_item_export);
    endfunction
endclass

//////////////////////////////////////////////////////////////////////////////////

class l140_env extends uvm_env;
    // Register to Factory
    `uvm_component_utils(l140_env);
    
    // Properties
    l140_agent a;
    l140_sequence seq1;
    
    // Constructor
    function new(string path = "ENV", uvm_component parent = null);
        super.new(path, parent);
    endfunction
    
    // Build Phase
    virtual function void build_phase(uvm_phase phase);
        super.build_phase(phase);
        a    = l140_agent::type_id::create("a", this);
        seq1 = l140_sequence::type_id::create("seq1", this);
    endfunction
    
    // Run Phase
    virtual task run_phase(uvm_phase phase);
        phase.raise_objection(this);
            seq1.start(this.a.seqr);
        phase.drop_objection(this);
    endtask
endclass

//////////////////////////////////////////////////////////////////////////////////

class l140_test extends uvm_test;
    // Register to Factory
    `uvm_component_utils(l140_test);
    
    // Properties
    l140_env e;
    
    // Constructor
    function new(string path = "TEST", uvm_component parent = null);
        super.new(path, parent);
    endfunction
    
    // Build Phase
    virtual function void build_phase(uvm_phase phase);
        super.build_phase(phase);
        e = l140_env::type_id::create("e", this);
    endfunction
endclass

//////////////////////////////////////////////////////////////////////////////////

module section8_140;
    initial begin
        run_test("l140_test");
    end
endmodule

