
axiom df-kb
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  assert |- ketbra = ( x e. ~H , y e. ~H |-> ( z e. ~H |-> ( ( z .ih y ) .h x ) ) )
end
