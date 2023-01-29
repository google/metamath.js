lexicon "lexicon.mm";

axiom ax1(wff x, wff y, wff z) : |- 'x t y - q z x' {
  assumes {
    ax1.1: |- 'x t y q z';
  }
}
