package FIFO_coverage_pkg;
	import uvm_pkg::*;
	import FIFO_seq_item_pkg::*;
	`include "uvm_macros.svh"

	class FIFO_coverage extends uvm_component;
		`uvm_component_utils(FIFO_coverage)
		uvm_analysis_export #(FIFO_seq_item) cov_export;
		uvm_tlm_analysis_fifo #(FIFO_seq_item) cov_fifo;
		FIFO_seq_item cov_seq_item;

		covergroup FIFO_cvg_gp;
			//Labeling coverpoints to be visible in the functional coverage report
			write_cp: 					coverpoint cov_seq_item.wr_en 		 		{bins wr_en[] 		 		 = {[0:1]};}
			read_cp: 					coverpoint cov_seq_item.rd_en 		 		{bins rd_en[] 		 		 = {[0:1]};}
			full_cp: 					coverpoint cov_seq_item.full  		 		{bins full[]  		 		 = {[0:1]};}
			empty_cp: 					coverpoint cov_seq_item.empty 		 		{bins empty[] 		 		 = {[0:1]};}
			almostfull_cp: 				coverpoint cov_seq_item.almostfull  		{bins almostfull[]   		 = {[0:1]};}
			almostempty_cp: 			coverpoint cov_seq_item.almostempty 		{bins almostempty[]  		 = {[0:1]};}
			overflow_cp: 				coverpoint cov_seq_item.overflow	 		{bins overflow[] 	 		 = {[0:1]};}
			underflow_cp: 				coverpoint cov_seq_item.underflow	 		{bins underflow[] 	 		 = {[0:1]};}
			wr_ack_cp: 					coverpoint cov_seq_item.wr_ack 	 			{bins wr_ack[] 	 	 		 = {[0:1]};}
			not_to_empty_cp: 			coverpoint cov_seq_item.empty				{bins not_to_empty 	 		 = (0=>1);}
 				 	
			write_seq_cp:				coverpoint cov_seq_item.wr_en 		 		{bins write_seq	 	 		 = (0=>1[*8]=>0);}
			read_seq_cp:				coverpoint cov_seq_item.rd_en 		 		{bins read_seq	 	 		 = (0=>1[*8]=>0);}
			empty_to_not_cp: 			coverpoint cov_seq_item.empty				{bins empty_to_not 	 		 = (1=>0);}
			full_to_not_cp: 			coverpoint cov_seq_item.full				{bins full_to_not 	 		 = (1=>0);}
			write_read_simlt_cp:		cross write_cp, read_cp 					{bins write_read_simlt 		 = binsof(write_cp.wr_en[1]) && binsof(read_cp.rd_en[1]); option.cross_auto_bin_max = 0;}
			full_to_empty_cp:			cross not_to_empty_cp, full_to_not_cp 		{bins full_to_empty 		 = binsof(full_to_not_cp) && binsof(not_to_empty_cp); option.cross_auto_bin_max = 0;}
			write_read_simlt_full_cp:	cross write_read_simlt_cp, full_cp 			{bins write_read_simlt_full  = binsof(write_read_simlt_cp) && binsof(full_cp.full[1]); option.cross_auto_bin_max = 0;}
			write_read_simlt_empty_cp:	cross write_read_simlt_cp, empty_cp 		{bins write_read_simlt_empty = binsof(write_read_simlt_cp) && binsof(empty_cp.empty[1]); option.cross_auto_bin_max = 0;}
			write_nor_read_cp:			cross write_cp, read_cp 					{bins write_read_simlt 		 = binsof(write_cp.wr_en[0]) && binsof(read_cp.rd_en[0]); option.cross_auto_bin_max = 0;}

			write_cross_states: cross write_cp, full_cp, empty_cp, almostfull_cp, almostempty_cp, overflow_cp, underflow_cp, wr_ack_cp {
				bins write_full = 		 binsof(write_cp) && binsof(full_cp);
				bins write_empty = 		 binsof(write_cp) && binsof(empty_cp);
				bins write_almostfull =  binsof(write_cp) && binsof(almostfull_cp);
				bins write_almostempty = binsof(write_cp) && binsof(almostempty_cp);
				bins write_overflow = 	 binsof(write_cp) && binsof(overflow_cp);
				bins write_underflow = 	 binsof(write_cp) && binsof(underflow_cp);
				bins write_wr_ack = 	 binsof(write_cp) && binsof(wr_ack_cp);
			}

			read_cross_states: cross read_cp, full_cp, empty_cp, almostfull_cp, almostempty_cp, overflow_cp, underflow_cp, wr_ack_cp {
				bins read_full = 		 binsof(read_cp) && binsof(full_cp);
				bins read_empty = 		 binsof(read_cp) && binsof(empty_cp);
				bins read_almostfull =   binsof(read_cp) && binsof(almostfull_cp);
				bins read_almostempty =  binsof(read_cp) && binsof(almostempty_cp);
				bins read_overflow = 	 binsof(read_cp) && binsof(overflow_cp);
				bins read_underflow = 	 binsof(read_cp) && binsof(underflow_cp);
				bins read_wr_ack = 		 binsof(read_cp) && binsof(wr_ack_cp);
			}
			
		endgroup : FIFO_cvg_gp

		function new(string name = "FIFO_coverage", uvm_component parent = null);
			super.new(name, parent);
			FIFO_cvg_gp = new();
		endfunction : new

		function void build_phase(uvm_phase phase);
			super.build_phase(phase);
			cov_export = new("cov_export", this);
			cov_fifo = new("cov_fifo", this);
		endfunction : build_phase

		function void connect_phase(uvm_phase phase);
			super.connect_phase(phase);
			cov_export.connect(cov_fifo.analysis_export);
		endfunction : connect_phase

		task run_phase(uvm_phase phase);
			super.run_phase(phase);
			forever begin
				cov_fifo.get(cov_seq_item);
				if(cov_seq_item.rst_n)
					FIFO_cvg_gp.sample();
			end
		endtask : run_phase
	endclass : FIFO_coverage
	
endpackage : FIFO_coverage_pkg