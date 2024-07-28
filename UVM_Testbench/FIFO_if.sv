interface FIFO_if #(
	parameter FIFO_WIDTH = 16,
	parameter FIFO_DEPTH = 8)(input bit clk);

	logic [FIFO_WIDTH-1:0] data_in;
	logic rst_n, wr_en, rd_en;
	logic [FIFO_WIDTH-1:0] data_out;
	logic wr_ack, overflow;
	logic full, empty, almostfull, almostempty, underflow;

	logic [FIFO_WIDTH-1:0] data_out_ref;
	logic wr_ack_ref, overflow_ref, full_ref, empty_ref, almostfull_ref, almostempty_ref, underflow_ref;

	modport DUT (
		input data_in, clk, rst_n, wr_en, rd_en,
		output data_out, wr_ack, overflow, full, empty, almostfull, almostempty, underflow
		);

	modport REF (
		input data_in, clk, rst_n, wr_en, rd_en,
		output data_out_ref, wr_ack_ref, overflow_ref, full_ref, empty_ref, almostfull_ref, almostempty_ref, underflow_ref
		);

	modport SVA (
		input data_in, clk, rst_n, wr_en, rd_en, data_out, wr_ack, overflow, full, empty, almostfull, almostempty, underflow
		);

endinterface : FIFO_if