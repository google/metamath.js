include "lexicon.mm"

axiom ax4
  let wff x
  let wff y
  ax4.1: assume |- x DND y
  assert |- x DND x y
end
