`include "uvm_macros.svh"
import uvm_pkg::*;

//////////////////////////////////////////////////////////////////////////////////

class l143_transaction extends uvm_sequence_item;
    // Properties
    rand bit [3:0] a;
    rand bit [3:0] b;
         bit [4:0] y;
    
    // Constructor
    function new(string inst = "l143_transaction");
        super.new(inst);
    endfunction

    // Field Macros
    `uvm_object_utils_begin(l143_transaction);
        `uvm_field_int(a, UVM_DEFAULT);
        `uvm_field_int(b, UVM_DEFAULT);
        `uvm_field_int(y, UVM_DEFAULT);
    `uvm_object_utils_end;
endclass

//////////////////////////////////////////////////////////////////////////////////

class l143_sequence extends uvm_sequence#(l143_transaction);
    // Register to Factory
    `uvm_object_utils(l143_sequence)
    
    // Properties
    l143_transaction trans;
    
    // Constructor
    function new(string inst = "l143_sequence");
        super.new(inst);
    endfunction

    // Body Task
    virtual task body();
        repeat(5) begin
           trans = l143_transaction::type_id::create("trans");
           start_item(trans);
           assert(trans.randomize());
           finish_item(trans);
           `uvm_info("SEQ", $sformatf("a: %0d | b: %0d", trans.a, trans.b), UVM_NONE); 
        end 
    endtask
endclass

//////////////////////////////////////////////////////////////////////////////////

class l143_driver extends uvm_driver#(l143_transaction);
    // Register to Factory
    `uvm_component_utils(l143_driver);      
    
    // Properties
    l143_transaction trans;         // data container
    
    // Constructor
    function new(string path = "DRV", uvm_component parent = null);
        super.new(path, parent);
    endfunction
    
    // Run Phase
    virtual task run_phase(uvm_phase phase);
        trans = l143_transaction::type_id::create("trans");
        forever begin
            seq_item_port.get_next_item(trans);
            `uvm_info("DRV", $sformatf("a: %0d | b: %0d", trans.a, trans.b), UVM_NONE);
            seq_item_port.item_done();
        end
    endtask
endclass

//////////////////////////////////////////////////////////////////////////////////

class l143_agent extends uvm_agent;
    // Register to Factory
    `uvm_component_utils(l143_agent);
    
    // Properties
    l143_driver d;
    uvm_sequencer #(l143_transaction) seqr;
    
    // Constructor
    function new(string path = "AGENT", uvm_component parent = null);
        super.new(path, parent);
    endfunction
    
    // Build Phase
    virtual function void build_phase(uvm_phase phase);
        super.build_phase(phase);
        d = l143_driver::type_id::create("d", this);
        seqr = uvm_sequencer#(l143_transaction)::type_id::create("seqr", this);
    endfunction
    
    // Connect Phase
    virtual function void connect_phase(uvm_phase phase);
        super.connect_phase(phase);
        d.seq_item_port.connect(seqr.seq_item_export);
    endfunction
endclass

//////////////////////////////////////////////////////////////////////////////////

class l143_env extends uvm_env;
    // Register to Factory
    `uvm_component_utils(l143_env);
    
    // Properties
    l143_agent a;
    l143_sequence seq1;
    
    // Constructor
    function new(string path = "ENV", uvm_component parent = null);
        super.new(path, parent);
    endfunction
    
    // Build Phase
    virtual function void build_phase(uvm_phase phase);
        super.build_phase(phase);
        a    = l143_agent::type_id::create("a", this);
        seq1 = l143_sequence::type_id::create("seq1", this);
    endfunction
    
    // Run Phase
    virtual task run_phase(uvm_phase phase);
        phase.raise_objection(this);
            seq1.start(this.a.seqr);
        phase.drop_objection(this);
    endtask
endclass

//////////////////////////////////////////////////////////////////////////////////

class l143_test extends uvm_test;
    // Register to Factory
    `uvm_component_utils(l143_test);
    
    // Properties
    l143_env e;
    
    // Constructor
    function new(string path = "TEST", uvm_component parent = null);
        super.new(path, parent);
    endfunction
    
    // Build Phase
    virtual function void build_phase(uvm_phase phase);
        super.build_phase(phase);
        e = l143_env::type_id::create("e", this);
    endfunction
endclass

//////////////////////////////////////////////////////////////////////////////////

module section8_143;
    initial begin
        run_test("l143_test");
    end
endmodule

