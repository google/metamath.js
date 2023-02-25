include "lexicon.mm"

axiom ax2
  let wff x
  let wff y
  let wff z
  assume ax2.1: |- x - t y - q z
  assert |- C z
end
