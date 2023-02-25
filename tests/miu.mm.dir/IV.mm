include "lexicon.mm"

axiom IV
  let wff x
  let wff y
  IVa: assume |- x U U y
  assert |- x y
end
