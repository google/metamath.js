include "lexicon.mm"

axiom ax1
  let wff x
  let wff y
  let wff z
  ax1.1: assume |- x t y q z
  assert |- x t y - q z x
end
