include "lexicon.mm"

axiom ax6
  let wx: wff x
  let wz: wff z
  assume ax6.1: |- z DF x
  assume ax6.2: |- x - DND z
  assert |- z DF x -
end
