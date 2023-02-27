include "lexicon.mm"

axiom ax5
  let wff z
  assume ax5.1: |- - - DND z
  assert |- z DF - -
end
