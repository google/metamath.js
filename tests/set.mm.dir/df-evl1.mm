
axiom df-evl1
  let vx: setvar x
  let vy: setvar y
  let vr: setvar r
  let vb: setvar b
  assert |- eval1 = ( r e. _V |-> [_ ( Base ` r ) / b ]_ ( ( x e. ( b ^m ( b ^m 1o ) ) |-> ( x o. ( y e. b |-> ( 1o X. { y } ) ) ) ) o. ( 1o eval r ) ) )
end
