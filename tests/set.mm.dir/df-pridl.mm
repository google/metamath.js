
axiom df-pridl
  let vx: setvar x
  let vy: setvar y
  let vi: setvar i
  let vr: setvar r
  let va: setvar a
  let vb: setvar b
  assert |- PrIdl = ( r e. RingOps |-> { i e. ( Idl ` r ) | ( i =/= ran ( 1st ` r ) /\ A. a e. ( Idl ` r ) A. b e. ( Idl ` r ) ( A. x e. a A. y e. b ( x ( 2nd ` r ) y ) e. i -> ( a C_ i \/ b C_ i ) ) ) } )
end
