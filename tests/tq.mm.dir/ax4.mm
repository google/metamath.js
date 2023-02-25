include "lexicon.mm"

axiom ax4
  let wff x
  let wff y
  assume ax4.1: |- x DND y
  assert |- x DND x y
end
