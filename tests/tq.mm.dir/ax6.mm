lexicon "lexicon.mm";

axiom ax6(wff x, wff z) : |- 'z DF x -' {
  assumes {
    ax6.1: |- 'z DF x';
    ax6.2: |- 'x - DND z';
  }
}
