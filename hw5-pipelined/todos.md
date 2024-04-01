## ONLY TESTING ADDI FOR SANITY 
* route alu_output to writeback stage 
* change regfile_we signal to propoagate through 

## PREP FOR SW OR LW INSNS 
* make a new always_comb block 
	- casing on memory_state.insn_m 
* is_mem_write/read signals --> validate them (TODO: make a addi, sw, lw) 


## BYPASSING 
## STALLING 