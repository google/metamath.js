
axiom df-drs
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vf: setvar f
  let vr: setvar r
  let vb: setvar b
  assert |- Dirset = { f e. Preset | [. ( Base ` f ) / b ]. [. ( le ` f ) / r ]. ( b =/= (/) /\ A. x e. b A. y e. b E. z e. b ( x r z /\ y r z ) ) }
end
