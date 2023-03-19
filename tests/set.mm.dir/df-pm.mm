
axiom df-pm
  let vx: setvar x
  let vy: setvar y
  let vf: setvar f
  assert |- ^pm = ( x e. _V , y e. _V |-> { f e. ~P ( y X. x ) | Fun f } )
end
