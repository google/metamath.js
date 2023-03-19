
axiom df-flf
  let vx: setvar x
  let vy: setvar y
  let vf: setvar f
  assert |- fLimf = ( x e. Top , y e. U. ran Fil |-> ( f e. ( U. x ^m U. y ) |-> ( x fLim ( ( U. x FilMap f ) ` y ) ) ) )
end
