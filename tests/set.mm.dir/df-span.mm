
axiom df-span
  let vx: setvar x
  let vy: setvar y
  assert |- span = ( x e. ~P ~H |-> |^| { y e. SH | x C_ y } )
end
