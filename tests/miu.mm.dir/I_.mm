include "lexicon.mm"

axiom I_
  let wx: wff x
  assume Ia: |- x I
  assert |- x I U
end
