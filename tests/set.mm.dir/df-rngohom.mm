
axiom df-rngohom
  let vx: setvar x
  let vy: setvar y
  let vf: setvar f
  let vs: setvar s
  let vr: setvar r
  assert |- RngHom = ( r e. RingOps , s e. RingOps |-> { f e. ( ran ( 1st ` s ) ^m ran ( 1st ` r ) ) | ( ( f ` ( GId ` ( 2nd ` r ) ) ) = ( GId ` ( 2nd ` s ) ) /\ A. x e. ran ( 1st ` r ) A. y e. ran ( 1st ` r ) ( ( f ` ( x ( 1st ` r ) y ) ) = ( ( f ` x ) ( 1st ` s ) ( f ` y ) ) /\ ( f ` ( x ( 2nd ` r ) y ) ) = ( ( f ` x ) ( 2nd ` s ) ( f ` y ) ) ) ) } )
end
