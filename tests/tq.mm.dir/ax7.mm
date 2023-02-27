include "lexicon.mm"

axiom ax7
  let wff z
  assume ax7.1: |- z - DF z
  assert |- P z -
end
