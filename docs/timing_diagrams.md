# Timing Diagrams

This chapter captures canonical timing scenarios for the RV32I core.  All diagrams use the [WaveDrom](https://wavedrom.com) JSON syntax so they can be rendered directly in documentation tools, yet remain readable as ASCII.

## 1. Single instruction through the pipeline

````wavedrom
{ "signal": [
  {"name":"clk", "wave":"p....."},
  {"name":"IF",  "wave":"=.....", "data":["I0"]},
  {"name":"ID",  "wave":".=....", "data":["I0"]},
  {"name":"EX",  "wave":"..=...", "data":["I0"]},
  {"name":"MEM", "wave":"...=..", "data":["I0"]},
  {"name":"WB",  "wave":"....=.", "data":["I0"]}
]}
````

Instruction `I0` advances one stage per cycle with no stalls or flushes.  Write-back completes in the fifth cycle after fetch.

## 2. Back-to-back independent instructions

````wavedrom
{ "signal": [
  {"name":"clk", "wave":"p......"},
  {"name":"IF",  "wave":"=.=...", "data":["I0","I1"]},
  {"name":"ID",  "wave":".=.=..", "data":["I0","I1"]},
  {"name":"EX",  "wave":"..=.=.", "data":["I0","I1"]},
  {"name":"MEM", "wave":"...=.=", "data":["I0","I1"]},
  {"name":"WB",  "wave":"....=.", "data":["I0"]},
  {"name":"WB",  "wave":".....=", "data":["I1"]}
]}
````

Independent instructions stream through the pipe each cycle; the MEM stage simply forwards the ALU result for `I0` while `I1` executes behind it.

## 3. Read-after-write hazard with optional forwarding

The main pipeline does not yet integrate the forwarding logic, but the standalone `rv32i_forwarding_unit` demonstrates the intended behaviour.  The timeline below assumes that unit is wired between MEM/WB and EX.

````wavedrom
{ "signal": [
  {"name":"clk", "wave":"p......."},
  {"name":"IF",  "wave":"=.=....", "data":["ADD","SUB"]},
  {"name":"ID",  "wave":".=.=...", "data":["ADD","SUB"]},
  {"name":"EX",  "wave":"..=.=..", "data":["ADD","SUB"]},
  {"name":"MEM", "wave":"...=.=.", "data":["ADD","SUB"]},
  {"name":"WB",  "wave":"....=..", "data":["ADD"]},
  {"name":"ForwardA", "wave":"..01.0.", "data":["none","mem","none"]}
]}
````

`ForwardA` switches to `mem` while the SUB instruction is in EX, providing the ADD result without inserting bubbles.

## 4. Load-use hazard with MEM-induced stall

````wavedrom
{ "signal": [
  {"name":"clk", "wave":"p........"},
  {"name":"IF",  "wave":"=.=.=...", "data":["LW","ADD","NOP"]},
  {"name":"ID",  "wave":".=..=...", "data":["LW","ADD"]},
  {"name":"EX",  "wave":"..=..=..", "data":["LW","ADD"]},
  {"name":"MEM", "wave":"...=....", "data":["LW"]},
  {"name":"pipeline_hold", "wave":"...1...0"},
  {"name":"data_rvalid", "wave":".....10."}
]}
````

When the load issues, `pipeline_hold` goes high until `data_rvalid` returns.  The dependent ADD instruction remains in ID/EX and only advances once the data arrives.

## 5. Branch taken with flush

````wavedrom
{ "signal": [
  {"name":"clk", "wave":"p......."},
  {"name":"IF",  "wave":"=.=.=..", "data":["BEQ","I1","I2"]},
  {"name":"ID",  "wave":".=.=...", "data":["BEQ","I1"]},
  {"name":"EX",  "wave":"..=....", "data":["BEQ"]},
  {"name":"branch_taken", "wave":"..1...."},
  {"name":"flush_if", "wave":"..1...."},
  {"name":"flush_id", "wave":"..1...."},
  {"name":"redirect_pc", "wave":"..=....", "data":["target"]}
]}
````

`I1` and `I2` are flushed from IF/ID when the branch resolves.  Fetch restarts at the redirect PC during the next cycle.

## 6. Instruction fetch Wishbone transaction

````wavedrom
{ "signal": [
  {"name":"clk", "wave":"p......"},
  {"name":"instr_req", "wave":"0.1.0.", "phase":0},
  {"name":"instr_gnt", "wave":"0.10..", "phase":1},
  {"name":"instr_rvalid", "wave":"0...10", "phase":3},
  {"name":"wb_cyc", "wave":"0.1110"},
  {"name":"wb_stb", "wave":"0.1110"},
  {"name":"wb_ack", "wave":"0...10"}
]}
````

The IF stage asserts `instr_req`; the adapter raises `wb_cyc`/`wb_stb` until the ROM responds with `wb_ack`, which in turn triggers `instr_rvalid`.

## 7. Data load Wishbone transaction

````wavedrom
{ "signal": [
  {"name":"clk", "wave":"p......."},
  {"name":"data_req", "wave":"0.1....", "phase":0},
  {"name":"data_we", "wave":"0.0...."},
  {"name":"ex_hold", "wave":"0.111100"},
  {"name":"wb_cyc", "wave":"0.11110."},
  {"name":"wb_stb", "wave":"0.11110."},
  {"name":"wb_ack", "wave":"0....10"},
  {"name":"data_rvalid", "wave":"0....10"}
]}
````

The MEM stage stalls the pipeline via `ex_hold` until `wb_ack` returns, at which point `data_rvalid` is asserted and the hold deasserts.

## 8. Data store Wishbone transaction

````wavedrom
{ "signal": [
  {"name":"clk", "wave":"p......"},
  {"name":"data_req", "wave":"0.1.0.."},
  {"name":"data_we", "wave":"0.1.0.."},
  {"name":"data_be[3:0]", "wave":"0.=.0..", "data":["0b0011"]},
  {"name":"wb_cyc", "wave":"0.11.0."},
  {"name":"wb_stb", "wave":"0.11.0."},
  {"name":"wb_ack", "wave":"0..10."}
]}
````

Stores are single-cycle: once the adapter accepts the request the pipeline continues, even though the Wishbone acknowledgement may arrive a cycle later.

## 9. Back-to-back memory operations

````wavedrom
{ "signal": [
  {"name":"clk", "wave":"p........."},
  {"name":"data_req", "wave":"0.1..1...", "data":[null,null]},
  {"name":"data_we", "wave":"0.0..1..."},
  {"name":"wb_cyc", "wave":"0.1111110"},
  {"name":"wb_ack", "wave":"0...10.10"},
  {"name":"data_rvalid", "wave":"0...10..0"},
  {"name":"store_complete", "wave":"0.....10."}
]}
````

A load is followed immediately by a store.  The data adapter serialises the transactions: the second request only begins after the first acknowledgement completes.

## 10. Register file concurrent read/write

````wavedrom
{ "signal": [
  {"name":"clk", "wave":"p....."},
  {"name":"rd_we", "wave":"0.1.0."},
  {"name":"rd_addr", "wave":"x.=.x.", "data":["x7"]},
  {"name":"rd_wdata", "wave":"x.=.x.", "data":["0x1234"]},
  {"name":"rs1_addr", "wave":"=.==..", "data":["x5","x7"]},
  {"name":"rs1_data", "wave":"x.=.==", "data":["old","0x1234"]}
]}
````

When `rs1_addr` matches `rd_addr` in the cycle of the write, the register file bypasses `rd_wdata` to the read port, guaranteeing the latest value is observed.

## 11. Register file write-through behaviour across cycles

````wavedrom
{ "signal": [
  {"name":"clk", "wave":"p......"},
  {"name":"rd_we", "wave":"0.10..."},
  {"name":"rd_addr", "wave":"x.=0..", "data":["x10"]},
  {"name":"rd_wdata", "wave":"x.=0..", "data":["0xDEAD"]},
  {"name":"rs2_addr", "wave":"0.==0..", "data":["x11","x10"]},
  {"name":"rs2_data", "wave":"x.0=0..", "data":["old","0xDEAD"]}
]}
````

`rs2_addr` switches to `x10` the cycle after the write occurs; the new data is immediately visible thanks to the asynchronous read ports.

---

These timing references complement the structural information in [`architecture.md`](architecture.md) and the interface tables in [`module_interfaces.md`](module_interfaces.md).  When modifying the pipeline or bus protocols, update the relevant diagrams to reflect the new behaviour.
