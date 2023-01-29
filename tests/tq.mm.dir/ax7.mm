lexicon "lexicon.mm";

axiom ax7(wff z) : |- 'P z -' {
  assumes {
    ax7.1: |- 'z - DF z';
  }
}
