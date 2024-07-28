package FIFO_write_sequence_pkg;
	import uvm_pkg::*;
	import FIFO_seq_item_pkg::*;
	`include "uvm_macros.svh"

	class FIFO_write_sequence extends uvm_sequence #(FIFO_seq_item);
		`uvm_object_utils(FIFO_write_sequence)

		FIFO_seq_item seq_item;

		function new(string name = "FIFO_write_sequence");
			super.new(name);
		endfunction : new

		task body();
			repeat(500) begin
				seq_item = FIFO_seq_item::type_id::create("seq_item");
				seq_item.Simultaneous_Read_Write.constraint_mode(0);
				seq_item.WR_EN_ON_DIST = 90; seq_item.RD_EN_ON_DIST = 10; seq_item.RST_ON_DIST = 5;
				start_item(seq_item);
				assert(seq_item.randomize());
				finish_item(seq_item);
			end
		endtask : body
	endclass : FIFO_write_sequence
	
endpackage : FIFO_write_sequence_pkg