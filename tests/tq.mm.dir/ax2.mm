include "lexicon.mm"

axiom ax2
  let wx: wff x
  let wy: wff y
  let wz: wff z
  assume ax2.1: |- x - t y - q z
  assert |- C z
end
