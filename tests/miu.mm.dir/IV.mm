lexicon "lexicon.mm";

axiom IV(wff x, wff y) : |- x y {
  assumes {
    IVa: |- x U U y
  }
}
