include "lexicon.mm"

axiom a1
  let tt: term t
  let tr: term r
  let ts: term s
  assert |- ( t = r -> ( t = s -> r = s ) )
end
