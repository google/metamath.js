
axiom df-r1
  let vx: setvar x
  assert |- R1 = rec ( ( x e. _V |-> ~P x ) , (/) )
end
