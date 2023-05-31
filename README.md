> This is not an officially supported Google product

Typogram (short for typographic programs) is a programming language that only operates with typographic derivations. It is intended to be used to represent and verify derivations in axiomatic systems (e.g. mathematical derivations). 

Typogram borrows from [metamath](https://metamath.org) its verification system, and can be transpiled to (i.e. they can be verified with) and from (to a smaller extent) metamath. It extends metamath in providing program modularization, so that large source files can be broken into smaller ones. It borrows from [Isabelle's](https://en.wikipedia.org/wiki/Isabelle_(proof_assistant)) its familiar syntax.

Here is an example of a a typogram that verify SK combinators:

```
axiom term-k() {
  return term K;
}

axiom term-s() {
  return term S;
}

axiom term-c(term p, term q) {
  return term p [ q ];
}

axiom word-c(word w, word c) {
  return word w c;
}

axiom word-null() {
  return word $$;
}

axiom word-t(term x) {
  return word $x$;
}

axiom word-l() {
  return word [;
}

axiom word-r() {
  return word ];
}

// If Δ is a derivation ending in an expression of the form α((Kβ)γ)ι,
// then Δ followed by the term αβι is a derivation.
axiom ax-k(word head, term x, term y, word tail) {
  assume |- head K [ x ] [ y ] tail;
  return |- head x tail;
}

// If Δ is a derivation ending in an expression of the form α(((Sβ)γ)δ)ι,
// then Δ followed by the term α((βδ)(γδ))ι is a derivation.
axiom ax-s(word head, term x, term y, term z, word tail) {
  assume |- head S [ x ] [ y ] [ z ] tail;
  return |- head x [ z ] [ y [ z ] ] tail;
}

axiom df-eq(word head, term x, term y, word tail) {
  assume |- x = y;
  assume |- head x tail;
  return |- head y tail;
}

axiom df-sym(word head, term x, term y, word tail) {
  assume |- head x = y tail;
  return |- head y = x tail;
}

axiom df-eqid(term x) {
  return |- x = x;
}

axiom df-id() {
  return |- I = S [ K ] [ K ];
}

axiom term-i() {
  return term I;
}

theorem id(
  id.fh: word head,
  id.f0: term x,
  id.ft: word tail) {

  assume id.e0: |- head I [ x ] tail;

  do {
    id.fh;
    id.f0;
    term-k;
    id.f0;
    term-c;
    id.ft;

      id.fh;
      term-k;
      term-k;
      id.f0;
      id.ft;

          id.fh;

          term-i;

          term-s;
          term-k;
          term-c;
          term-k;
          term-c;

          word-l;

          id.f0;
          word-t;
          word-c;

          word-r;
          word-c;

          id.ft;
          word-c;

          df-id;

          id.e0;

          df-eq;

      ax-s;

    ax-k;
  };

  return |- head x tail;
}
```

Here are a few examples of Typograms running in browsers:

- [Schönfinkel's SK](https://code.sgo.to/2023/03/23/sk.html)
- [Hofstader's MIU](https://code.sgo.to/2022/04/12/hofstadter-miu.html)
- [Hofstader's PQ](https://code.sgo.to/2022/04/13/hofstadter-pq.html)
- [2 + 2 = 4?](https://code.sgo.to/2022/11/26/2p2e4.html)
- [Verifying Set.mm](https://code.sgo.to/2022/11/26/set.mm.html)


