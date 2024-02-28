`include "uvm_macros.svh"
import uvm_pkg::*;

//////////////////////////////////////////////////////////////////////////////////

class l138_transaction extends uvm_sequence_item;
    // Properties
    rand bit [3:0] a;
    rand bit [3:0] b;
         bit [4:0] y;
    
    // Constructor
    function new(string inst = "l138_transaction");
        super.new(inst);
    endfunction

    // Field Macros
    `uvm_object_utils_begin(l138_transaction);
        `uvm_field_int(a, UVM_DEFAULT);
        `uvm_field_int(b, UVM_DEFAULT);
        `uvm_field_int(y, UVM_DEFAULT);
    `uvm_object_utils_end;
endclass

//////////////////////////////////////////////////////////////////////////////////

class l138_sequence extends uvm_sequence#(l138_transaction);
    // Register to Factory
    `uvm_object_utils(l138_sequence)
    
    // Properties
    l138_transaction trans;
    
    // Constructor
    function new(string inst = "l138_sequence");
        super.new(inst);
    endfunction

    // Body Task
    virtual task body();
        `uvm_info("SEQ", "Trans obj created", UVM_NONE);
        trans = l138_transaction::type_id::create("trans");
        
        `uvm_info("SEQ", "Waiting for Grant from Driver", UVM_NONE);
        wait_for_grant();
        
        `uvm_info("SEQ", "Rcvd Grant .. Randomizing Data", UVM_NONE);
        assert(trans.randomize());
        
        `uvm_info("SEQ", "Randomization Done -> Sent Req to Driver", UVM_NONE);
        send_request(trans);
        
        `uvm_info("SEQ", "Waiting for Item Done Resp from Driver", UVM_NONE);
        wait_for_item_done();
        
        `uvm_info("SEQ", "SEQ Ended", UVM_NONE);
    endtask
endclass

//////////////////////////////////////////////////////////////////////////////////

class l138_driver extends uvm_driver#(l138_transaction);
    // Register to Factory
    `uvm_component_utils(l138_driver);      
    
    // Properties
    l138_transaction t;
    
    // Constructor
    function new(string path = "DRV", uvm_component parent = null);
        super.new(path, parent);
    endfunction
    
    // Build Phase
    virtual function void build_phase(uvm_phase phase);
        super.build_phase(phase);
        t = l138_transaction::type_id::create("t");
//        if(!uvm_config_db#(virtual adder_if)::get(this, "", "aif", aif))
//            `uvm_info("DRV", "Unable to access Interface", UVM_NONE)
    endfunction
    
    // Run Phase
    virtual task run_phase(uvm_phase phase);
        forever begin
            `uvm_info("DRV", "Sending Grant for Sequence", UVM_NONE);
            seq_item_port.get_next_item(t);
            
            `uvm_info("DRV", "Applying Seq to DUT", UVM_NONE);
            /* ..Apply stilumlus to DUT */
            
            `uvm_info("DRV", "Sending Item Done Resp for Sequence", UVM_NONE);
            seq_item_port.item_done();
        end
    endtask
endclass

//////////////////////////////////////////////////////////////////////////////////

class l138_agent extends uvm_agent;
    // Register to Factory
    `uvm_component_utils(l138_agent);
    
    // Properties
    l138_driver d;
    uvm_sequencer #(l138_transaction) seqr;
    
    // Constructor
    function new(string path = "AGENT", uvm_component parent = null);
        super.new(path, parent);
    endfunction
    
    // Build Phase
    virtual function void build_phase(uvm_phase phase);
        super.build_phase(phase);
        d = l138_driver::type_id::create("d", this);
        seqr = uvm_sequencer#(l138_transaction)::type_id::create("seqr", this);
    endfunction
    
    // Connect Phase
    virtual function void connect_phase(uvm_phase phase);
        super.connect_phase(phase);
        d.seq_item_port.connect(seqr.seq_item_export);
    endfunction
endclass

//////////////////////////////////////////////////////////////////////////////////

class l138_env extends uvm_env;
    // Register to Factory
    `uvm_component_utils(l138_env);
    
    // Properties
    l138_agent a;
    
    // Constructor
    function new(string path = "ENV", uvm_component parent = null);
        super.new(path, parent);
    endfunction
    
    // Build Phase
    virtual function void build_phase(uvm_phase phase);
        super.build_phase(phase);
        a = l138_agent::type_id::create("a", this);
    endfunction
endclass

//////////////////////////////////////////////////////////////////////////////////

class l138_test extends uvm_test;
    // Register to Factory
    `uvm_component_utils(l138_test);
    
    // Properties
    l138_env e;
    l138_sequence seq1;
    
    // Constructor
    function new(string path = "TEST", uvm_component parent = null);
        super.new(path, parent);
    endfunction
    
    // Build Phase
    virtual function void build_phase(uvm_phase phase);
        super.build_phase(phase);
        e = l138_env::type_id::create("e", this);
        seq1 = l138_sequence::type_id::create("seq1");
    endfunction
    
    // Run Phase
    virtual task run_phase(uvm_phase phase);
        phase.raise_objection(this);
            seq1.start(this.e.a.seqr);
        phase.drop_objection(this);
    endtask
endclass

//////////////////////////////////////////////////////////////////////////////////

module section8_138;
    initial begin
        run_test("l138_test");
    end
endmodule

