include "lexicon.mm"

axiom III
  let wff x
  let wff y
  IIIa: assume |- x I I I y
  assert |- x U y
end
