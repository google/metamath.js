
axiom df-chj
  let vx: setvar x
  let vy: setvar y
  assert |- vH = ( x e. ~P ~H , y e. ~P ~H |-> ( _|_ ` ( _|_ ` ( x u. y ) ) ) )
end
