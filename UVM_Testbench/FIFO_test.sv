package FIFO_test_pkg;
	import uvm_pkg::*;
	import FIFO_env_pkg::*;
	import FIFO_config_pkg::*;
	import FIFO_reset_sequence_pkg::*;
	import FIFO_write_sequence_pkg::*;
	import FIFO_read_sequence_pkg::*;
	import FIFO_concurrent_sequence_pkg::*;
	import FIFO_simult_sequence_pkg::*;
	`include "uvm_macros.svh"
	
	class FIFO_test extends uvm_test;
		`uvm_component_utils(FIFO_test)

		FIFO_env env;
		FIFO_config FIFO_cfg;
		FIFO_reset_sequence reset_seq;
		FIFO_write_sequence write_seq;
		FIFO_read_sequence read_seq;
		FIFO_concurrent_sequence concurrent_seq;
		FIFO_simult_sequence simult_seq;

		function new(string name = "FIFO_test", uvm_component parent = null);
			super.new(name, parent);
		endfunction : new

		function void build_phase(uvm_phase phase);
			super.build_phase(phase);
			env = FIFO_env::type_id::create("env", this);
			FIFO_cfg = FIFO_config::type_id::create("FIFO_cfg", this);
			reset_seq = FIFO_reset_sequence::type_id::create("reset_seq", this);
			write_seq = FIFO_write_sequence::type_id::create("write_seq", this);
			read_seq = FIFO_read_sequence::type_id::create("read_seq", this);
			concurrent_seq = FIFO_concurrent_sequence::type_id::create("concurrent_seq", this);
			simult_seq = FIFO_simult_sequence::type_id::create("simult_seq", this);

			if(!uvm_config_db#(virtual FIFO_if)::get(this, "", "FIFO_IF", FIFO_cfg.FIFO_vif)) //get the vif and assign it to the vif of the cfg
				`uvm_fatal("build_phase", "Test - Unable to get the virtual interface of the FIFO from the uvm_config_db")

			uvm_config_db#(FIFO_config)::set(this, "*", "CFG", FIFO_cfg);
		endfunction : build_phase

		task run_phase(uvm_phase phase);
			super.run_phase(phase);
			phase.raise_objection(this);
			//reset sequence
			`uvm_info("run_phase", "Reset Asserted", UVM_LOW)
			reset_seq.start(env.agt.sqr);
			`uvm_info("run_phase", "Reset Deasserted", UVM_LOW)

			//write sequence
			`uvm_info("run_phase", "Write Sequence Started", UVM_LOW)
			write_seq.start(env.agt.sqr);
			`uvm_info("run_phase", "Write Sequence Ended", UVM_LOW)

			//read sequence
			`uvm_info("run_phase", "Read Sequence Started", UVM_LOW)
			read_seq.start(env.agt.sqr);
			`uvm_info("run_phase", "Read Sequence Ended", UVM_LOW)

			//concurrent sequence
			`uvm_info("run_phase", "Concurrent Sequence Started", UVM_LOW)
			concurrent_seq.start(env.agt.sqr);
			`uvm_info("run_phase", "Concurrent Sequence Ended", UVM_LOW)

			//simult sequence
			`uvm_info("run_phase", "Simultaneous Sequence Started", UVM_LOW)
			simult_seq.start(env.agt.sqr);
			`uvm_info("run_phase", "Simultaneous Sequence Ended", UVM_LOW)
			phase.drop_objection(this);
		endtask : run_phase
		
	endclass : FIFO_test

endpackage : FIFO_test_pkg