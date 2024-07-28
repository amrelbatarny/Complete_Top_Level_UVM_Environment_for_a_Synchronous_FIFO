module FIFO_SVA (FIFO_if.SVA FIFOif);

	assert_overflow_fall: assert property (@(posedge FIFOif.clk) disable iff (!FIFOif.rst_n) (FIFOif.full |=> (FIFOif.wr_en && FIFOif.rd_en) |-> ##2 (!FIFOif.overflow)));
	cover_overflow_fall: cover property (@(posedge FIFOif.clk) disable iff (!FIFOif.rst_n) (FIFOif.full |=> (FIFOif.wr_en && FIFOif.rd_en) |-> ##2 (!FIFOif.overflow)));

	assert_underflow_fall: assert property (@(posedge FIFOif.clk) disable iff (!FIFOif.rst_n) (FIFOif.empty |=> (FIFOif.wr_en && FIFOif.rd_en) |-> ##2 (!FIFOif.underflow)));
	cover_underflow_fall: cover property (@(posedge FIFOif.clk) disable iff (!FIFOif.rst_n) (FIFOif.empty |=> (FIFOif.wr_en && FIFOif.rd_en) |-> ##2 (!FIFOif.underflow)));

	assert_wr_ack_full: assert property (@(posedge FIFOif.clk) disable iff (!FIFOif.rst_n) (FIFOif.full |=> (!FIFOif.wr_ack)));
	cover_wr_ack_full: cover property (@(posedge FIFOif.clk) disable iff (!FIFOif.rst_n) (FIFOif.full |=> (!FIFOif.wr_ack)));

	assert_almostfe: assert property (@(posedge FIFOif.clk) disable iff (!FIFOif.rst_n) (FIFOif.almostfull |-> !FIFOif.almostempty));
	cover_almostfe: cover property (@(posedge FIFOif.clk) disable iff (!FIFOif.rst_n) (FIFOif.almostfull |-> !FIFOif.almostempty));

	assert_almostef: assert property (@(posedge FIFOif.clk) disable iff (!FIFOif.rst_n) (FIFOif.almostempty |-> !FIFOif.almostfull));
	cover_almostef: cover property (@(posedge FIFOif.clk) disable iff (!FIFOif.rst_n) (FIFOif.almostempty |-> !FIFOif.almostfull));

	assert_full_empty: assert property (@(posedge FIFOif.clk) disable iff (!FIFOif.rst_n) (!(FIFOif.full && FIFOif.empty)));
	cover_full_empty: cover property (@(posedge FIFOif.clk) disable iff (!FIFOif.rst_n) (!(FIFOif.full && FIFOif.empty)));

	assert_write_full: assert property (@(posedge FIFOif.clk) disable iff (!FIFOif.rst_n) (FIFOif.full && FIFOif.wr_en) |=> !FIFOif.wr_ack);
	cover_write_full: cover property (@(posedge FIFOif.clk) disable iff (!FIFOif.rst_n) (FIFOif.full && FIFOif.wr_en) |=> !FIFOif.wr_ack);

endmodule : FIFO_SVA