include "lexicon.mm"

axiom ax2
  let wff x
  let wff y
  let wff z
  ax2.1: assume |- x - t y - q z
  assert |- C z
end
