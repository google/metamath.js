
axiom ax-arg
  let wva0: term a0
  let wva1: term a1
  let wva2: term a2
  let wvb0: term b0
  let wvb1: term b1
  let wvb2: term b2
  assume arg.1: |- ( ( a0 v b0 ) ^ ( a1 v b1 ) ) =< ( a2 v b2 )
  assert |- ( ( a0 v a1 ) ^ ( b0 v b1 ) ) =< ( ( ( a0 v a2 ) ^ ( b0 v b2 ) ) v ( ( a1 v a2 ) ^ ( b1 v b2 ) ) )
end
