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
