`include "uvm_macros.svh"
import uvm_pkg::*;
////////////////////////////////////////////////////////////////////////////
class comp extends uvm_component;
    // Register class to Factory
    `uvm_component_utils(comp)
    
    // Constructor
    function new(string path = "comp", uvm_component parent = null);
        super.new(path, parent);
    endfunction
    
    // build phase
    virtual function void build_phase(uvm_phase phase);
        super.build_phase(phase);
        `uvm_info("COMP", "Build phase of comp complete", UVM_NONE)
    endfunction
endclass
