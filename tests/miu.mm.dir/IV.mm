include "lexicon.mm"

axiom IV
  let wx: wff x
  let wy: wff y
  assume IVa: |- x U U y
  assert |- x y
end
