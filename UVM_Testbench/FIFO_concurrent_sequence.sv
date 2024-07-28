package FIFO_concurrent_sequence_pkg;
	import uvm_pkg::*;
	import FIFO_seq_item_pkg::*;
	`include "uvm_macros.svh"

	class FIFO_concurrent_sequence extends uvm_sequence #(FIFO_seq_item);
		`uvm_object_utils(FIFO_concurrent_sequence)

		FIFO_seq_item seq_item1;
		FIFO_seq_item seq_item2;

		function new(string name = "FIFO_concurrent_sequence");
			super.new(name);
		endfunction : new

		task body();
			repeat(100) begin
				repeat(10) begin
					seq_item1 = FIFO_seq_item::type_id::create("seq_item1");
					seq_item1.Simultaneous_Read_Write.constraint_mode(0);
					seq_item1.WR_EN_ON_DIST = 90; seq_item1.RD_EN_ON_DIST = 10; seq_item1.RST_ON_DIST = 2;
					start_item(seq_item1);
					assert(seq_item1.randomize());
					finish_item(seq_item1);
				end

				repeat(10) begin
					seq_item2 = FIFO_seq_item::type_id::create("seq_item2");
					seq_item2.Simultaneous_Read_Write.constraint_mode(0);
					seq_item2.WR_EN_ON_DIST = 10; seq_item2.RD_EN_ON_DIST = 90; seq_item2.RST_ON_DIST = 2;
					start_item(seq_item2);
					assert(seq_item2.randomize());
					finish_item(seq_item2);
				end
			end
		endtask : body
	endclass : FIFO_concurrent_sequence
	
endpackage : FIFO_concurrent_sequence_pkg