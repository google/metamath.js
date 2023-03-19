
axiom df-idl
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vi: setvar i
  let vr: setvar r
  assert |- Idl = ( r e. RingOps |-> { i e. ~P ran ( 1st ` r ) | ( ( GId ` ( 1st ` r ) ) e. i /\ A. x e. i ( A. y e. i ( x ( 1st ` r ) y ) e. i /\ A. z e. ran ( 1st ` r ) ( ( z ( 2nd ` r ) x ) e. i /\ ( x ( 2nd ` r ) z ) e. i ) ) ) } )
end
