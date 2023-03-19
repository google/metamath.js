
axiom df-pjh
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vh: setvar h
  assert |- projh = ( h e. CH |-> ( x e. ~H |-> ( iota_ z e. h E. y e. ( _|_ ` h ) x = ( z +h y ) ) ) )
end
