# HoPDR: a collection of nuHFL(Z) solvers

This repository contains some nuHFL(Z) (aka higher-order CHC) solvers, a fixpoint logic for higher-order program verification:
- HoPDR: A higher-order extension of Property-Directed Reachability
- ModeTrans: A testing framework for disproving fixpoint logic formulas with mode-guided transformation to functional programs


## Input Format Specification


```
%HES
𝒞₁;
𝒞₂;
⋮
𝒞ₙ;
```

where 𝒞₁ is the top-level formula and 
```
atom := false | true | n
φ := atom | x | φ₁ <op> φ₂ | φ₁ <pred> φ₂ | φ₁ \/ φ₂ | φ₁ /\ φ₂ | φ₁ t | φ₁ φ₂ | ∀x. φ | \x. φ
𝒞 := X x₁ ⋯ xₙ =v φ
op := + | - | *
pred := < | <= | > | >= | != | =
```

[Examples](hopdr/inputs)

## HoPDR


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

### Input Format

In addition to the above syntax, you can input SMT2Lib CHCs with the option `--chc`.

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




