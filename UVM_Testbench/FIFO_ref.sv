module FIFO_ref(FIFO_if.REF FIFOif);
	logic [FIFOif.FIFO_WIDTH-1:0] mem[$];
	bit wr_ack_next, wr_ack_next1;

	always @(posedge FIFOif.clk or negedge FIFOif.rst_n) begin
		if(~FIFOif.rst_n) begin
			mem.delete();
			FIFOif.overflow_ref <= 0;
			FIFOif.wr_ack_ref <= 0;
		end
		else begin
			if(FIFOif.wr_en) begin
				if(!FIFOif.full_ref) begin
					mem.push_front(FIFOif.data_in);
					FIFOif.wr_ack_ref <= 1;
					FIFOif.overflow_ref <= 0;
				end else begin
					FIFOif.wr_ack_ref <= 0;
					FIFOif.overflow_ref <= 1;
				end
			end else begin
				FIFOif.wr_ack_ref <= 0;
				FIFOif.overflow_ref <= 0;
			end
		end
	end

	always @(posedge FIFOif.clk or negedge FIFOif.rst_n) begin
		if(~FIFOif.rst_n) begin
			mem.delete();
			FIFOif.data_out_ref <= 0;
			FIFOif.underflow_ref <= 0;
		end
		else begin
			if(FIFOif.rd_en) begin
				if(!FIFOif.empty_ref) begin
					FIFOif.data_out_ref <= mem.pop_back();
					FIFOif.underflow_ref <= 0;
				end else begin
					FIFOif.underflow_ref <= 1;
				end
			end else
				FIFOif.underflow_ref <= 0;
		end
	end

	always_comb begin
		case(mem.size())
			0:
			begin
				FIFOif.full_ref = 0;
				FIFOif.almostfull_ref = 0;
				FIFOif.empty_ref = 1;
				FIFOif.almostempty_ref = 0;
			end
			1:
			begin
				FIFOif.full_ref = 0;
				FIFOif.almostfull_ref = 0;
				FIFOif.empty_ref = 0;
				FIFOif.almostempty_ref = 1;
			end
			FIFOif.FIFO_DEPTH-1:
			begin
				FIFOif.full_ref = 0;
				FIFOif.almostfull_ref = 1;
				FIFOif.empty_ref = 0;
				FIFOif.almostempty_ref = 0;
			end
			FIFOif.FIFO_DEPTH:
			begin
				FIFOif.full_ref = 1;
				FIFOif.almostfull_ref = 0;
				FIFOif.empty_ref = 0;
				FIFOif.almostempty_ref = 0;
			end
			default:
			begin
				FIFOif.full_ref = 0;
				FIFOif.almostfull_ref = 0;
				FIFOif.empty_ref = 0;
				FIFOif.almostempty_ref = 0;
			end
		endcase // mem.size()
	end

endmodule