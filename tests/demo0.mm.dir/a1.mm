
axiom a1
  param tt: term t
  param tr: term r
  param ts: term s
  assert |- ( t = r -> ( t = s -> r = s ) )
end
