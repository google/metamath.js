include "lexicon.mm"
include "t.mm"
include "r.mm"
include "s.mm"

axiom a1
  assert |- ( t = r -> ( t = s -> r = s ) )
end
