# hopdr

## Build

```
cargo build --release
```

## Debug

### Log

You can tern on the debug output by using `RUST_LOG=...`.

Ex)
```
RUST_BACKTRACE=1 RUST_LOG="warn,hopdr::solver=debug" cargo run
```
