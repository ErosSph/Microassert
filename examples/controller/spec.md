# Controller fixture specification

This is an original test fixture, not a CPU or an architectural reference model.
All state changes use the rising edge of clk. Reset rst_n is active low.
Reset clears busy, done, data_o and decoded and sets the state to IDLE.
The legal states are IDLE (0), ACTIVE (1), COMPLETE (2).
In IDLE, sampling start accepts a request, captures data_i in data_o and sets busy.
An accepted request advances to ACTIVE on the next sample, then COMPLETE,
then IDLE. done is set on leaving COMPLETE and cleared in IDLE.
busy is cleared on leaving COMPLETE. Requests outside IDLE do not start work.
decoded reflects whether opcode sampled on the preceding active clock was 2.
No fairness or input stability assumptions are required by this fixture.
