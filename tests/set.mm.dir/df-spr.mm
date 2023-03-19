
axiom df-spr
  let vv: setvar v
  let vp: setvar p
  let va: setvar a
  let vb: setvar b
  assert |- Pairs = ( v e. _V |-> { p | E. a e. v E. b e. v p = { a , b } } )
end
