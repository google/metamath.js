
axiom df-oc
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  assert |- _|_ = ( x e. ~P ~H |-> { y e. ~H | A. z e. x ( y .ih z ) = 0 } )
end
