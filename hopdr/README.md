# hopdr 
## Build

```
cargo build --release
```

## Debug

### Log

You can turn on the debug output by using `RUST_LOG=...`.

#### ex1: enable smt/chc solvers log with rust backtrace

```
RUST_BACKTRACE=1 RUST_LOG="warn,hopdr::solver=debug" cargo run
```

#### ex2: enable PDR's output

```
RUST_LOG="hopdr::pdr::pdr=debug" cargo run
```


## install deps

Currently, hopdr is highly dependent on relative path to external binaries.
This issue is to be fixed.

Required dependencies:
- interpolation solver
  - smtinterpol (assume: `~/.local/share/hopdr/smtinterpol.jar`)
- CHC solver
  - hoice
- SMTSolver
  - z3
- Misc
  - Java (for smtinterpol)

```
wget  http://ultimate.informatik.uni-freiburg.de/smtinterpol/smtinterpol-2.5-1093-g7506c07c.jar -O ~/.local/share/hopdr/smtinterpol.jar
```

## clippy

```
$ cargo clippy -- -D warnings -A clippy::upper-case-acronyms
```
