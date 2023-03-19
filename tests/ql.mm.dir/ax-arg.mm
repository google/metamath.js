
axiom ax-arg
  param wva0: term a0
  param wva1: term a1
  param wva2: term a2
  param wvb0: term b0
  param wvb1: term b1
  param wvb2: term b2
  assume arg.1: |- ( ( a0 v b0 ) ^ ( a1 v b1 ) ) =< ( a2 v b2 )
  assert |- ( ( a0 v a1 ) ^ ( b0 v b1 ) ) =< ( ( ( a0 v a2 ) ^ ( b0 v b2 ) ) v ( ( a1 v a2 ) ^ ( b1 v b2 ) ) )
end
