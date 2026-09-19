# Using external CPU designs

CPU sources and SPEC snapshots are intentionally not redistributed in this
release. Clone the desired upstream version into the ignored `benchmarks/`
directory and configure its exact file list, top, includes, reset and SPEC.
Review each upstream license before redistributing any derivative artifact.

The research workspace used these upstream projects:

| Design | Upstream | Typical top |
|---|---|---|
| PicoRV32 | https://github.com/YosysHQ/picorv32 | `picorv32` |
| TinyRISC-V | https://github.com/liangkangnan/tinyriscv | `tinyriscv` |
| ultraembedded RISC-V | https://github.com/ultraembedded/riscv | check selected revision |
| ultraembedded biRISC-V | https://github.com/ultraembedded/biriscv | check selected revision |
| E203 | https://github.com/riscv-mcu/e203_hbirdv2 | `e203_cpu_top` |

These links identify projects, not a promise that current HEAD reproduces past
experiments. Record a commit hash and SPEC revision. Top/module macros and
configuration materially change the coverage denominator. Do not compare a
CPU-only run with a SoC hierarchy without stating the difference.

For a first CPU run, adapt `configs/example.yaml`, use a fresh output directory,
and run `doctor` and `analyze` before paying for LLM/formal stages. Supply all
required RTL dependencies in the correct order. There is no bundled proprietary
tool, hidden benchmark checkout or private-directory fallback.
