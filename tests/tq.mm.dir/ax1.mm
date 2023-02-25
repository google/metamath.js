include "lexicon.mm"

axiom ax1
  let wff x
  let wff y
  let wff z
  assume ax1.1: |- x t y q z
  assert |- x t y - q z x
end
