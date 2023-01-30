lexicon "lexicon.mm";

axiom ax1(wff x, wff y, wff z) : |- "x p y - q z -" {
  assumes {
    ax1.1: |- "x p y q z";
  }
}
