
axiom df-ray
  let vx: setvar x
  let vn: setvar n
  let vr: setvar r
  let vp: setvar p
  let va: setvar a
  assert |- Ray = { <. <. p , a >. , r >. | E. n e. NN ( ( p e. ( EE ` n ) /\ a e. ( EE ` n ) /\ p =/= a ) /\ r = { x e. ( EE ` n ) | p OutsideOf <. a , x >. } ) }
end
