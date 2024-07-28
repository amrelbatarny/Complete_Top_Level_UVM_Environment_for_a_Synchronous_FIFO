vlib work
vlog -f src_files.list -mfcu +cover +define+SIM
vsim -voptargs=+acc work.FIFO_top -classdebug -uvmcontrol=all -cover +UVM_VERBOSITY=UVM_MEDIUM +UVM_NO_RELNOTES
add wave    -color red		sim:/FIFO_top/FIFOif/clk
add wave     				sim:/FIFO_top/FIFOif/rst_n
add wave     				sim:/FIFO_top/FIFOif/wr_en
add wave     				sim:/FIFO_top/FIFOif/rd_en
add wave     				sim:/FIFO_top/FIFOif/data_in
add wave    -color cyan		sim:/FIFO_top/FIFOif/data_out
add wave    -color gold		sim:/FIFO_top/FIFOif/data_out_ref
add wave    -color cyan		sim:/FIFO_top/FIFOif/wr_ack
add wave    -color gold		sim:/FIFO_top/FIFOif/wr_ack_ref
add wave   	-color cyan		sim:/FIFO_top/FIFOif/full
add wave   	-color gold		sim:/FIFO_top/FIFOif/full_ref
add wave   	-color cyan		sim:/FIFO_top/FIFOif/empty
add wave   	-color gold		sim:/FIFO_top/FIFOif/empty_ref
add wave   	-color cyan		sim:/FIFO_top/FIFOif/almostfull
add wave   	-color gold		sim:/FIFO_top/FIFOif/almostfull_ref
add wave   	-color cyan		sim:/FIFO_top/FIFOif/almostempty
add wave   	-color gold		sim:/FIFO_top/FIFOif/almostempty_ref
add wave   	-color cyan		sim:/FIFO_top/FIFOif/overflow
add wave   	-color gold		sim:/FIFO_top/FIFOif/overflow_ref
add wave   	-color cyan		sim:/FIFO_top/FIFOif/underflow
add wave   	-color gold		sim:/FIFO_top/FIFOif/underflow_ref
add wave   	-color blue		sim:/FIFO_top/DUT/mem
add wave   	-color blue		sim:/FIFO_top/DUT/count
add wave   	-color blue		sim:/FIFO_top/DUT/wr_ptr
add wave   	-color blue		sim:/FIFO_top/DUT/rd_ptr
add wave 					sim:/FIFO_top/DUT/FIFO_SVA_inst/assert_overflow_fall
add wave 					sim:/FIFO_top/DUT/FIFO_SVA_inst/assert_underflow_fall
add wave 					sim:/FIFO_top/DUT/FIFO_SVA_inst/assert_wr_ack_full
add wave 					sim:/FIFO_top/DUT/FIFO_SVA_inst/assert_almostfe
add wave 					sim:/FIFO_top/DUT/FIFO_SVA_inst/assert_almostef
add wave 					sim:/FIFO_top/DUT/FIFO_SVA_inst/assert_full_empty
add wave 					sim:/FIFO_top/DUT/FIFO_SVA_inst/assert_write_full
add wave   			 		sim:/FIFO_top/DUT/assert_full
add wave   			 		sim:/FIFO_top/DUT/assert_empty
add wave   			 		sim:/FIFO_top/DUT/assert_almostfull
add wave   			 		sim:/FIFO_top/DUT/assert_almostempty
add wave   			 		sim:/FIFO_top/DUT/assert_overflow
add wave   			 		sim:/FIFO_top/DUT/assert_underflow
add wave   			 		sim:/FIFO_top/DUT/assert_wr_ack
add wave   			 		sim:/FIFO_top/DUT/assert_count_incr
add wave   			 		sim:/FIFO_top/DUT/assert_count_decr
add wave   			 		sim:/FIFO_top/DUT/assert_wr_ptr_incr
add wave   			 		sim:/FIFO_top/DUT/assert_rd_ptr_incr
add wave   			 		sim:/FIFO_top/DUT/assert_count_rst
add wave   			 		sim:/FIFO_top/DUT/assert_wr_ptr_rst
add wave   			 		sim:/FIFO_top/DUT/assert_rd_ptr_rst
add wave   			 		sim:/FIFO_top/DUT/assert_write_pointer_stable
add wave   			 		sim:/FIFO_top/DUT/assert_read_pointer_stable
add wave   			 		sim:/FIFO_top/DUT/assert_data_out_rst
add wave   			 		sim:/FIFO_top/DUT/assert_overflow_rst
add wave   			 		sim:/FIFO_top/DUT/assert_underflow_rst
add wave   			 		sim:/FIFO_top/DUT/assert_wr_ack_rst
.vcop Action toggleleafnames
coverage save FIFO_tb.ucdb -onexit -du FIFO
run -all
#coverage report -detail -cvg -directive -comments -output seqcover_report.txt /.
#coverage report -detail -cvg -directive -comments -output fcover_report.txt {}
#quit -sim
#vcover report FIFO_tb.ucdb -details -annotate -all -output coverage_rpt.txt
