
axiom df-poset
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vf: setvar f
  let vr: setvar r
  let vb: setvar b
  assert |- Poset = { f | E. b E. r ( b = ( Base ` f ) /\ r = ( le ` f ) /\ A. x e. b A. y e. b A. z e. b ( x r x /\ ( ( x r y /\ y r x ) -> x = y ) /\ ( ( x r y /\ y r z ) -> x r z ) ) ) }
end
