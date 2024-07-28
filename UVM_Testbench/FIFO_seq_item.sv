package FIFO_seq_item_pkg;
	import uvm_pkg::*;
	`include "uvm_macros.svh"

	parameter VALID_OP = 6;
	typedef enum bit [2:0] {OR, XOR, ADD, MULT, SHIFT, ROTATE, INVALID_6, INVALID_7} opcode_e;
	typedef enum {MAXPOS = 3, ZERO = 0, MAXNEG = -4} reg_e;
	

	class FIFO_seq_item extends uvm_sequence_item;
		`uvm_object_utils(FIFO_seq_item)

		parameter FIFO_WIDTH = 16;
		parameter FIFO_DEPTH = 8;

		//inputs
		rand logic [FIFO_WIDTH-1:0] data_in;
		rand logic rst_n, wr_en, rd_en;

		//outputs
		rand logic [FIFO_WIDTH-1:0] data_out;
		rand logic wr_ack, overflow;
		rand logic full, empty, almostfull, almostempty, underflow;

		//reference model outputs
		rand logic [FIFO_WIDTH-1:0] data_out_ref;
		rand logic wr_ack_ref, overflow_ref, full_ref, empty_ref, almostfull_ref, almostempty_ref, underflow_ref;

		function new(string name = "FIFO_seq_item");
			super.new(name);
		endfunction : new

		function string convert2string();
			return $sformatf("%s rst_n = 0b%0b, wr_en = 0b%0b, rd_en = 0b%0b, data_in = 0b%0b\n
				, data_out = 0b%0b, wr_ack = 0b%0b, overflow = 0b%0b, full = 0b%0b\n
				, empty = 0x%0h, almostfull = 0x%0h, almostempty = 0x%0h, underflow = 0x%0h", super.convert2string, rst_n, wr_en, rd_en, data_in, data_out, wr_ack, overflow, full, empty, almostfull, almostempty, underflow);
		endfunction : convert2string
			
		function string convert2string_stimulus();
			return $sformatf("rst_n = 0b%0b, wr_en = 0b%0b, rd_en = 0b%0b, data_in = 0b%0b", rst_n, wr_en, rd_en, data_in);
		endfunction : convert2string_stimulus

		int WR_EN_ON_DIST, RD_EN_ON_DIST, RST_ON_DIST;

		constraint Reset_Constraint {
			rst_n dist {1:=(100-RST_ON_DIST), 0:=RST_ON_DIST};
		}

		constraint General_Constraints {
			wr_en dist {1:=WR_EN_ON_DIST, 0:=(100-WR_EN_ON_DIST)};
			rd_en dist {1:=RD_EN_ON_DIST, 0:=(100-RD_EN_ON_DIST)};
			(full == 1)  -> wr_en dist {1:=80, 0:=20};
			(empty == 1) -> rd_en dist {1:=80, 0:=20};
			unique {data_in};
		}

		constraint Simultaneous_Read_Write {
			(wr_en && rd_en) dist {1:=80, 0:=20};
			(full == 1)  -> wr_en dist {1:=80, 0:=20};
			(empty == 1) -> rd_en dist {1:=80, 0:=20};
			unique {data_in};
		}

	endclass : FIFO_seq_item
	
endpackage : FIFO_seq_item_pkg