lexicon "lexicon.mm";

axiom ax2(wff x, wff y, wff z) : |- C z {
  assumes {
    ax2.1: |- x - t y - q z
  }
}
