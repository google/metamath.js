
axiom df-bra
  let vx: setvar x
  let vy: setvar y
  assert |- bra = ( x e. ~H |-> ( y e. ~H |-> ( y .ih x ) ) )
end
