lexicon "lexicon.mm";

axiom ax4(wff x, wff y) : |- 'x DND x y' {
  assumes {
    ax4.1: |- 'x DND y';
  }
}
