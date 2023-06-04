> This is not an officially supported Google product

Typogram (short for typographic programs) is an experimental programming language that can represent verifiable derivations in axiomatic systems (e.g. mathematical proofs). 

Typogram borrows from [metamath](https://metamath.org) its verification system and simplicity, and can be transpiled to (i.e. they can be verified with) and from (to a smaller extent) metamath. It extends metamath to provide modularization, so that large source files can be broken into smaller ones. It constraints metamath's syntax so that it can borrow some of the familiar syntax from [Isabelle](https://en.wikipedia.org/wiki/Isabelle_(proof_assistant)).

Here is an example of a a typogram that verifies the first theorem of Hofstader's PQ system:

```js
// "-" is a wff (well-formed formula)
axiom w0() {
  return wff "-";
}

// if x is a wff, then "w -" is a wff
axiom w1(wff x) {
  return wff "x -";
}

// "- -" is a wff
theorem t0() {
  do {
    w0;	w1;
  };
  return wff "- -";
}
```

Here are a few examples of Typograms running in browsers:

- [Schönfinkel's SK](https://code.sgo.to/2023/03/23/sk.html)
- [Hofstader's MIU](https://code.sgo.to/2022/04/12/hofstadter-miu.html)
- [Hofstader's PQ](https://code.sgo.to/2022/04/13/hofstadter-pq.html)
- [2 + 2 = 4?](https://code.sgo.to/2022/11/26/2p2e4.html)
- [Verifying Set.mm](https://code.sgo.to/2022/11/26/set.mm.html)


