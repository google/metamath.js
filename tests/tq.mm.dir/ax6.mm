include "lexicon.mm"
include "x.mm"
include "z.mm"

axiom ax6
  assume ax6.1: |- z DF x
  assume ax6.2: |- x - DND z  assert |- z DF x -
end
