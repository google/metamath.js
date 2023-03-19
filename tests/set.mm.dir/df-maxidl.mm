
axiom df-maxidl
  let vi: setvar i
  let vj: setvar j
  let vr: setvar r
  assert |- MaxIdl = ( r e. RingOps |-> { i e. ( Idl ` r ) | ( i =/= ran ( 1st ` r ) /\ A. j e. ( Idl ` r ) ( i C_ j -> ( j = i \/ j = ran ( 1st ` r ) ) ) ) } )
end
