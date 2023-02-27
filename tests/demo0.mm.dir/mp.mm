include "lexicon.mm"
include "P.mm"
include "Q.mm"

axiom mp
  assume min: |- P
  assume maj: |- ( P -> Q )  assert |- Q
end
