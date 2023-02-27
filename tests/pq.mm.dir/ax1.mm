include "lexicon.mm"
include "x.mm"
include "y.mm"
include "z.mm"

axiom ax1
  assume ax1.1: |- x p y q z  assert |- x p y - q z -
end
