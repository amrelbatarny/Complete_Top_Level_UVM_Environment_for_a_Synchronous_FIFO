import uvm_pkg::*;
import FIFO_test_pkg::*;
`include "uvm_macros.svh"

module FIFO_top ();
	bit clk;

	initial begin
		forever #1 clk = ~clk;
	end

	FIFO_if FIFOif(clk);
	FIFO DUT(FIFOif);
	FIFO_ref REF(FIFOif);
	bind FIFO FIFO_SVA FIFO_SVA_inst(FIFOif);


	initial begin
		uvm_config_db#(virtual FIFO_if)::set(null, "uvm_test_top", "FIFO_IF", FIFOif);
		run_test("FIFO_test");
	end
endmodule : FIFO_top