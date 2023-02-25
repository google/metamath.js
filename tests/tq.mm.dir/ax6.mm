include "lexicon.mm"

axiom ax6
  let wff x
  let wff z
  ax6.1: assume |- z DF x
  ax6.2: assume |- x - DND z
  assert |- z DF x -
end
