include "lexicon.mm"

axiom II
  let wff x
  assume IIa: |- M x
  assert |- M x x
end
