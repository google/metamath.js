include "lexicon.mm"

axiom II
  let wff x
  IIa: assume |- M x
  assert |- M x x
end
