include "lexicon.mm"

axiom IV
  let wff x
  let wff y
  assume IVa: |- x U U y
  assert |- x y
end
