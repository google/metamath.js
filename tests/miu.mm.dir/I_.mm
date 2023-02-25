include "lexicon.mm"

axiom I_
  let wff x
  Ia: assume |- x I
  assert |- x I U
end
