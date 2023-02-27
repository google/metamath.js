include "lexicon.mm"

axiom a1
  let term t
  let term r
  let term s
  assert |- ( t = r -> ( t = s -> r = s ) )
end
