include "lexicon.mm"

axiom mp
  let wff P
  let wff Q
  assume min: |- P
  assume maj: |- ( P -> Q )
  assert |- Q
end
