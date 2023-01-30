lexicon "lexicon.mm";

axiom I_(wff x) : |- "x I U" {
  assumes {
    Ia: |- "x I";
  }
}
