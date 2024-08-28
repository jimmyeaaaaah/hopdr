FROM ubuntu:22.04

RUN apt update && apt upgrade -y && apt install -y opam wget zip curl openjdk-11-jdk z3 libglpk-dev bubblewrap python3 python3-pip

RUN opam init -a -y && eval $(opam env)

ENV PATH="/root/.cargo/bin:${PATH}"

RUN mkdir /misc /root/bin

WORKDIR /misc

# Ultimate Eliminator
RUN wget "https://starexec.org/starexec/secure/download?token=94640982&type=solver&id=44761" -O /misc/ue.zip \
    && unzip ue.zip \
    && chmod +x /misc/UltimateEliminator+MathSAT-5.6.9/Ultimate/jdk-11.0.2/bin/java \
    && chmod +x /misc/UltimateEliminator+MathSAT-5.6.9/Ultimate/mathsat
ENV ULTIMATE_DIR=/misc/UltimateEliminator+MathSAT-5.6.9/Ultimate

# SMT Interpol
RUN mkdir -p ~/.local/share/hopdr/ &&  wget  http://ultimate.informatik.uni-freiburg.de/smtinterpol/smtinterpol-2.5-1093-g7506c07c.jar -O ~/.local/share/hopdr/smtinterpol.jar

# Rust
RUN curl --proto '=https' --tlsv1.2 -sSf https://sh.rustup.rs | sh -s -- -y

# ocamlformat
RUN opam install -y ocamlformat dune

# csisat
RUN eval $(opam env) \
   && git clone https://github.com/hopv/MoCHi /misc/MoCHi \
   && cd /misc/MoCHi \
   && git checkout b0ac0d626d64b1e3c779d8e98cb232121cc3196a \
   && cd /misc/MoCHi/csisat \
   && dune build --root . \
   && cp /misc/MoCHi/csisat/_build/default/bin/csisatMain.exe /root/bin/csisat

ENV PATH="/root/bin":$PATH

# hoice
RUN git clone https://github.com/hopv/hoice /misc/hoice\
    && cd /misc/hoice && git checkout v1.10.0 \
    && cargo build --release \
    && cp /misc/hoice/target/release/hoice /root/bin/hoice

# for hopdr's bin
ENV PATH="/work/bin":$PATH
