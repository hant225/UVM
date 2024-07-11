`timescale 1ns / 1ps
`include "uvm_macros.svh"
import uvm_pkg::*;

package pkg;
	localparam num1 = 3000;
	localparam num2 = 4000;
endpackage

////////////////////////////////////////////////////////////////////////////////////////////////

class base_seq_item extends uvm_sequence_item;
    
    // Properties
    logic [31:0] addr;
    logic [63:0] data;
  	logic [31:0] sum;
  	logic [31:0] sub;
    
    // Constructor
    function new(input string path = "base_seq_item");
        super.new(path);
    endfunction
    
    // Field Macros
    `uvm_object_utils_begin(base_seq_item)
        `uvm_field_int(addr, UVM_DEFAULT | UVM_DEC)
        `uvm_field_int(data, UVM_DEFAULT | UVM_DEC)
  		`uvm_field_int(sum,  UVM_DEFAULT | UVM_DEC)  	
  		`uvm_field_int(sub,  UVM_DEFAULT | UVM_DEC)  	
    `uvm_object_utils_end

        
  	// Display method
    function display();
      `uvm_info("base_seq_item", $sformatf("addr=%0d , data=%0d , sum=%0d, sub=%0d", this.addr, this.data, this.sum, this.sub), UVM_NONE)
    endfunction
endclass

////////////////////////////////////////////////////////////////////////////////////////////////

class child_seq_item extends base_seq_item;
    
    // Properties
    logic [15:0] ack;
    
    // Constructor
    function new(input string path = "child_seq_item");
        super.new(path);      	
    endfunction
    
    // Field Macros
  	`uvm_object_utils_begin(child_seq_item)
  		`uvm_field_int(ack, UVM_DEFAULT | UVM_DEC)
    `uvm_object_utils_end
       
  	// Display method
    function display();
      `uvm_info("child_seq_item", $sformatf("addr=%0d , data=%0d , sum=%0d, sub=%0d, ack=%0d", 
                             this.addr, this.data, this.sum, this.sub, this.ack), UVM_NONE)      
    endfunction
endclass

////////////////////////////////////////////////////////////////////////////////////////////////

class base_sequence #(parameter pA = 79,
                      parameter pB = 10) extends uvm_sequence#(base_seq_item);      	
  
  	// Factory Registry
  	`uvm_object_utils(base_sequence)  	
  

  	// Properties
  	base_seq_item tr;
  
  	// Constructor
    function new(input string path = "base_sequence");
      super.new(path);
    endfunction

      // Body task
    virtual task body();
      tr = base_seq_item::type_id::create("tr");
      load_value(tr);
      tr.display();
      tr.addr = 1;
      tr.data = 1;
      tr.display();
    endtask
  
  	virtual task load_value(base_seq_item tr);      	
    	tr.addr = 1000;
        tr.data = 999;      	
      	tr.sum  = pA + pB;
      	side_task(tr);
    endtask
        
  	virtual task side_task(base_seq_item tr);    // virtual keyword help base class call child class side_task's method
		tr.sub = pB - pA;
    endtask
endclass

////////////////////////////////////////////////////////////////////////////////////////////////
class child_sequence#(localparam pA = pkg::num1,
                      localparam pB = pkg::num2 ) extends base_sequence #(.pA(pkg::num1), .pB(pkg::num2));  
  
  	// Factory Registry
  	`uvm_object_utils(child_sequence)
  
  	// Properties
  	child_seq_item tr;
  
  	// Constructor
    function new(input string path = "child_sequence");
      super.new(path);
    endfunction

      // Body task
    virtual task body();      
      tr = child_seq_item::type_id::create("tr");
      load_value(tr);
      tr.ack = 777;
      tr.display();
      tr.print();
    endtask
  
    task load_value(base_seq_item tr);
      super.load_value(tr);      
    endtask
        
  	task side_task(base_seq_item tr);
		tr.sub = pB * pA;
    endtask
endclass

////////////////////////////////////////////////////////////////////////////////////////////////

class test extends uvm_test;
  
  // Field Macros
  `uvm_component_utils(test)
  
  // Properties  
  child_sequence cs;
  
  // Constructor
    function new(input string path = "TEST", uvm_component parent = null);
        super.new(path, parent);       
    endfunction
    
    // Build Phase
    virtual function void build_phase(uvm_phase phase);
        super.build_phase(phase);
      	//set_type_override_by_type(base_seq_item::get_type(), child_seq_item::get_type());
      set_type_override_by_type(base_sequence#()::get_type(), child_sequence#()::get_type());
      cs = child_sequence#()::type_id::create("cs");         	 
    endfunction
    
    // Run Phase
    virtual task run_phase(uvm_phase phase);        
        phase.raise_objection(this);
      		cs.start(null);
		    #10      		
        phase.drop_objection(this);
    endtask
  
endclass

////////////////////////////////////////////////////////////////////////////////////////////////

module test2;			    
  
    initial begin
      run_test("test");
    end

endmodule