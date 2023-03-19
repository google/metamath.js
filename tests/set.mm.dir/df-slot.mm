
axiom df-slot
  let vx: setvar x
  let cA: class A
  assert |- Slot A = ( x e. _V |-> ( x ` A ) )
end
