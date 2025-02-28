package FIFO_agent_pkg;
	import uvm_pkg::*;
	import FIFO_sequencer_pkg::*;
	import FIFO_driver_pkg::*;
	import FIFO_monitor_pkg::*;
	import FIFO_config_pkg::*;
	import FIFO_seq_item_pkg::*;
	`include "uvm_macros.svh"

	class FIFO_agent extends uvm_agent;
		`uvm_component_utils(FIFO_agent)
		FIFO_sequencer sqr;
		FIFO_driver driver;
		FIFO_monitor monitor;
		FIFO_config FIFO_cfg;
		uvm_analysis_port #(FIFO_seq_item) agt_ap;

		function new(string name = "FIFO_agent", uvm_component parent = null);
			super.new(name, parent);
		endfunction : new

		function void build_phase(uvm_phase phase);
			super.build_phase(phase);
			if(!uvm_config_db#(FIFO_config)::get(this, "", "CFG", FIFO_cfg)) //get the cfg from the db and assign it to the cfg of the driver
				`uvm_fatal("build_phase", "Agent - Unable to get the configuration object")
			
			sqr = FIFO_sequencer::type_id::create("sqr", this);
			driver = FIFO_driver::type_id::create("driver", this);
			monitor = FIFO_monitor::type_id::create("monitor", this);

			agt_ap = new("agt_ap", this);
		endfunction : build_phase

		function void connect_phase(uvm_phase phase);
			super.connect_phase(phase);
			driver.FIFO_vif = FIFO_cfg.FIFO_vif;
			monitor.FIFO_vif = FIFO_cfg.FIFO_vif;
			driver.seq_item_port.connect(sqr.seq_item_export);
			monitor.mon_ap.connect(agt_ap);
		endfunction : connect_phase
		
	endclass : FIFO_agent
	
endpackage : FIFO_agent_pkg