

vlib work
vlog -sv 10_examples_Boolean_exp.sv
vsim -voptargs=+acc work.examples_Boolean_exp
add wave -position insertpoint sim:/examples_Boolean_exp/*
run -all