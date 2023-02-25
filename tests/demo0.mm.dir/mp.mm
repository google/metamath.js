include "lexicon.mm"

axiom mp
  let wff P
  let wff Q
  min: assume |- P
  maj: assume |- ( P -> Q )
  assert |- Q
end
