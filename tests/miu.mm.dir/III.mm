lexicon "lexicon.mm";

axiom III(wff x, wff y) : |- x U y {
  assumes {
    IIIa: |- x I I I y
  }
}
