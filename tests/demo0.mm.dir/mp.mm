lexicon "lexicon.mm";

axiom mp(wff P, wff Q) : |- Q {
  assumes {
    min: |- P
    maj: |- ( P -> Q )
  }
}
