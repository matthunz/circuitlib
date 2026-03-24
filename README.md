# circuitlib

A circuit verification library for Lean4.

[Documentation](https://matt.hunzinger.me/circuitlib/docs)

## Roadmap

### Circuits

#### Combinational

- Logic Gates
  - [x] AND Gate
  - [x] OR Gate
  - [x] NOT Gate
  - [x] NAND Gate
  - [x] NOR Gate
  - [x] XOR Gate
  - [ ] XNOR Gate
- Arithmetic Circuits
  - [x] Half Adder
  - [ ] Full Adder
  - [ ] Ripple Carry Adder
  - [ ] Carry Lookahead Adder
  - [ ] Half Subtractor
  - [ ] Full Subtractor
  - [ ] Multiplier
- Data Routing
  - [ ] Multiplexer (MUX)
  - [ ] Demultiplexer (DEMUX)
  - [ ] Encoder
  - [ ] Decoder
  - [ ] Priority Encoder
- Comparison & Conversion
  - [ ] Magnitude Comparator
  - [ ] Binary to Gray Code Converter
  - [ ] Gray to Binary Converter
  - [ ] BCD to 7-Segment Decoder

### Sequential

- Latches
  - [ ] SR Latch
  - [ ] D Latch
- Flip-Flops
  - [ ] SR Flip-Flop
  - [ ] D Flip-Flop
  - [ ] JK Flip-Flop
  - [ ] T Flip-Flop
  - [ ] Master-Slave Flip-Flop
- Registers
  - [ ] Serial-In Serial-Out (SISO) Shift Register
  - [ ] Serial-In Parallel-Out (SIPO) Shift Register
  - [ ] Parallel-In Serial-Out (PISO) Shift Register
  - [ ] Parallel-In Parallel-Out (PIPO) Shift Register
  - [ ] Universal Shift Register
- Counters
  - [ ] Asynchronous (Ripple) Counter
  - [ ] Synchronous Counter
  - [ ] Up/Down Counter
  - [ ] Mod-N Counter
  - [ ] Ring Counter
  - [ ] Johnson Counter
- Memory
  - [ ] ROM (Read-Only Memory)
  - [ ] SRAM Cell
  - [ ] FIFO Buffer

### State Machines

- [ ] Mealy Machine
- [ ] Moore Machine

## Usage

`lakefile.toml`:

```toml
[[require]]
name = "circuitlib"
scope = "matthunz"
rev = "main"
```

`lakefile.lean`:

```lean4
require circuitlib from git "https://github.com/matthunz/circuitlib" @ "main"
```
