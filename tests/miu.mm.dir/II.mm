lexicon "lexicon.mm";

axiom II(wff x) : |- 'M x x' {
  assumes {
    IIa: |- 'M x';
  }
}
