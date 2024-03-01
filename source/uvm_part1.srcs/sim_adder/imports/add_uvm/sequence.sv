`timescale 1ns / 1ps
`include "uvm_macros.svh"
import uvm_pkg::*;

//////////////////////////////////////////////////////////////////////////////////

class sequence1 extends uvm_sequence#(transaction);
    // Register to Factory
    `uvm_object_utils(sequence1)
    
    // Properties
    transaction trans;
    
    // Constructor
    function new(string inst = "SEQ");
        super.new(inst);
    endfunction
    
    // Body
    virtual task body();
        trans = transaction::type_id::create("trans");
        
        repeat(100) begin
            `uvm_info("SEQ", "Sending transaction to DRV..", UVM_NONE)
            start_item(trans);
            trans.randomize();
            finish_item(trans);
            `uvm_info("SEQ", $sformatf("Transaction Info: a=%0d , b=%0d", trans.a, trans.b), UVM_NONE)
        end
    endtask
endclass

//////////////////////////////////////////////////////////////////////////////////



