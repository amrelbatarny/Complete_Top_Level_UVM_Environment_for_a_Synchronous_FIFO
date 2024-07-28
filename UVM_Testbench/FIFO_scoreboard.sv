package FIFO_scoreboard_pkg;
	import uvm_pkg::*;
	import FIFO_seq_item_pkg::*;
	`include "uvm_macros.svh"

	class FIFO_scoreboard extends uvm_scoreboard;
		`uvm_component_utils(FIFO_scoreboard)
		uvm_analysis_export #(FIFO_seq_item) sb_export;
		uvm_tlm_analysis_fifo #(FIFO_seq_item) sb_fifo;
		FIFO_seq_item sb_seq_item;

		int error_count;
		int correct_count;

		function new(string name = "FIFO_scoreboard", uvm_component parent = null);
			super.new(name, parent);
		endfunction : new

		function void build_phase(uvm_phase phase);
			super.build_phase(phase);
			sb_export = new("sb_export", this);
			sb_fifo = new("sb_fifo", this);
		endfunction : build_phase

		function void connect_phase(uvm_phase phase);
			super.connect_phase(phase);
			sb_export.connect(sb_fifo.analysis_export);
		endfunction : connect_phase
		
		task run_phase(uvm_phase phase);
			super.run_phase(phase);
			forever begin
				sb_fifo.get(sb_seq_item);

				if (sb_seq_item.data_out == sb_seq_item.data_out_ref)
					correct_count++;
				else begin
					`uvm_error("run_phase", $sformatf("Comparison failed, Transaction received by the DUT:%s
						While the data_out_ref:0x%0h", sb_seq_item.convert2string(), sb_seq_item.data_out_ref))
					error_count++;
					`uvm_error("run_phase", "data_out")
				end

				if (sb_seq_item.full === sb_seq_item.full_ref)
					correct_count++;
				else begin
					`uvm_error("run_phase", $sformatf("Comparison failed, Transaction received by the DUT:%s
						While the full_ref:0x%0h", sb_seq_item.convert2string(), sb_seq_item.full_ref))
					`uvm_error("run_phase", "full")
					error_count++;
				end
	
				if (sb_seq_item.empty === sb_seq_item.empty_ref)
					correct_count++;
				else begin
					`uvm_error("run_phase", $sformatf("Comparison failed, Transaction received by the DUT:%s
						While the empty_ref:0x%0h", sb_seq_item.convert2string(), sb_seq_item.empty_ref))
					error_count++;
					`uvm_error("run_phase", "empty")
				end
	
				if (sb_seq_item.almostfull === sb_seq_item.almostfull_ref)
					correct_count++;
				else begin
					`uvm_error("run_phase", $sformatf("Comparison failed, Transaction received by the DUT:%s
						While the almostfull_ref:0x%0h", sb_seq_item.convert2string(), sb_seq_item.almostfull_ref))
					error_count++;
					`uvm_error("run_phase", "almostfull")
				end
	
				if (sb_seq_item.almostempty === sb_seq_item.almostempty_ref)
					correct_count++;
				else begin
					`uvm_error("run_phase", $sformatf("Comparison failed, Transaction received by the DUT:%s
						While the almostempty_ref:0x%0h", sb_seq_item.convert2string(), sb_seq_item.almostempty_ref))
					error_count++;
				end
	
				if (sb_seq_item.overflow === sb_seq_item.overflow_ref)
					correct_count++;
				else begin
					`uvm_error("run_phase", $sformatf("Comparison failed, Transaction received by the DUT:%s
						While the overflow_ref:0x%0h", sb_seq_item.convert2string(), sb_seq_item.overflow_ref))
					error_count++;
				end
	
				if (sb_seq_item.underflow === sb_seq_item.underflow_ref)
					correct_count++;
				else begin
					`uvm_error("run_phase", $sformatf("Comparison failed, Transaction received by the DUT:%s
						While the underflow_ref:0x%0h", sb_seq_item.convert2string(), sb_seq_item.underflow_ref))
					error_count++;
				end
	
				if (sb_seq_item.wr_ack === sb_seq_item.wr_ack_ref)
					correct_count++;
				else begin
					`uvm_error("run_phase", $sformatf("Comparison failed, Transaction received by the DUT:%s
						While the wr_ack_ref:0x%0h", sb_seq_item.convert2string(), sb_seq_item.wr_ack_ref))
					error_count++;
				end
			end
		endtask : run_phase

		function void report_phase(uvm_phase phase);
			super.report_phase(phase);
			`uvm_info("report_phase", $sformatf("Total successful transactions: %0d", correct_count), UVM_LOW);
			`uvm_info("report_phase", $sformatf("Total failed transactions: %0d", error_count), UVM_LOW);
		endfunction : report_phase
	endclass : FIFO_scoreboard
	
endpackage : FIFO_scoreboard_pkg