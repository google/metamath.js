
axiom df-evls1
  let vx: setvar x
  let vy: setvar y
  let vs: setvar s
  let vr: setvar r
  let vb: setvar b
  assert |- evalSub1 = ( s e. _V , r e. ~P ( Base ` s ) |-> [_ ( Base ` s ) / b ]_ ( ( x e. ( b ^m ( b ^m 1o ) ) |-> ( x o. ( y e. b |-> ( 1o X. { y } ) ) ) ) o. ( ( 1o evalSub s ) ` r ) ) )
end
