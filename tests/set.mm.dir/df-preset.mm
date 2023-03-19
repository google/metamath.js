
axiom df-preset
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vf: setvar f
  let vr: setvar r
  let vb: setvar b
  assert |- Preset = { f | [. ( Base ` f ) / b ]. [. ( le ` f ) / r ]. A. x e. b A. y e. b A. z e. b ( x r x /\ ( ( x r y /\ y r z ) -> x r z ) ) }
end
