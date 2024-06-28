
# HoPDR: a collection of nuHFL(Z) solvers

This repository contains some nuHFL(Z) (aka higher-order CHC) solvers, a fixpoint logic for higher-order program verification:
- HoPDR: A higher-order extension of Property-Directed Reachability
- ModeTrans: A testing framework for disproving fixpoint logic formulas with mode-guided transformation to functional programs


TODO

## Input Format Specification

TODO

## HoPDR

TODO: 

### Requirements

- See [.github/workflows/test.yaml](.github/workflows/test.yaml) and [hopdr/docker/Dockerfile](hopdr/docker/Dockerfile) for the detail

### Manual Build

```
cargo run --release --bin hopdr
```


### How to Run

```
hopdr --input <filename>
```

## ModeTrans

### Requirements

- Ultimate Eliminator
- Z3
- ocamlopt
- ocamlformat

### Manual Build

```
cargo run --release --bin check
```

### How to Run


```
check --input <filename>
```




