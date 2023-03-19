
axiom df-al
  let hal: type al
  let vx: var x
  let vp: var p
  assert |- T. |= [ ! = \ p : ( al -> bool ) . [ p : ( al -> bool ) = \ x : al . T. ] ]
end
