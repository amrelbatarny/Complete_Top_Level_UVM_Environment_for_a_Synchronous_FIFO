package FIFO_monitor_pkg;
	import uvm_pkg::*;
	import FIFO_seq_item_pkg::*;
	`include "uvm_macros.svh"

	class FIFO_monitor extends uvm_monitor;
		`uvm_component_utils(FIFO_monitor)
		virtual FIFO_if FIFO_vif;
		FIFO_seq_item rsp_seq_item;
		uvm_analysis_port #(FIFO_seq_item) mon_ap;

		function new(string name = "FIFO_monitor", uvm_component parent = null);
			super.new(name, parent);
		endfunction : new

		function void build_phase(uvm_phase phase);
			super.build_phase(phase);
			mon_ap = new("mon_ap", this);
		endfunction : build_phase

		task run_phase(uvm_phase phase);
			super.run_phase(phase);
			forever begin
				rsp_seq_item = FIFO_seq_item::type_id::create("rsp_seq_item");
				@(negedge FIFO_vif.clk);
				rsp_seq_item.data_in = FIFO_vif.data_in;
				rsp_seq_item.rst_n = FIFO_vif.rst_n;
				rsp_seq_item.wr_en = FIFO_vif.wr_en;
				rsp_seq_item.rd_en = FIFO_vif.rd_en;
				rsp_seq_item.data_out = FIFO_vif.data_out;
				rsp_seq_item.wr_ack = FIFO_vif.wr_ack;
				rsp_seq_item.overflow = FIFO_vif.overflow;
				rsp_seq_item.full = FIFO_vif.full;
				rsp_seq_item.empty = FIFO_vif.empty;
				rsp_seq_item.almostfull = FIFO_vif.almostfull;
				rsp_seq_item.almostempty = FIFO_vif.almostempty;
				rsp_seq_item.underflow = FIFO_vif.underflow;
				rsp_seq_item.data_out_ref = FIFO_vif.data_out_ref;
				rsp_seq_item.wr_ack_ref = FIFO_vif.wr_ack_ref;
				rsp_seq_item.overflow_ref = FIFO_vif.overflow_ref;
				rsp_seq_item.full_ref = FIFO_vif.full_ref;
				rsp_seq_item.empty_ref = FIFO_vif.empty_ref;
				rsp_seq_item.almostfull_ref = FIFO_vif.almostfull_ref;
				rsp_seq_item.almostempty_ref = FIFO_vif.almostempty_ref;
				rsp_seq_item.underflow_ref = FIFO_vif.underflow_ref;
				mon_ap.write(rsp_seq_item);
				`uvm_info("run_phase", rsp_seq_item.convert2string(), UVM_HIGH)
			end
		endtask : run_phase
	endclass : FIFO_monitor
	
endpackage : FIFO_monitor_pkg