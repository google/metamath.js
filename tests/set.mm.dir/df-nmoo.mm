
axiom df-nmoo
  let vx: setvar x
  let vz: setvar z
  let vw: setvar w
  let vu: setvar u
  let vt: setvar t
  assert |- normOpOLD = ( u e. NrmCVec , w e. NrmCVec |-> ( t e. ( ( BaseSet ` w ) ^m ( BaseSet ` u ) ) |-> sup ( { x | E. z e. ( BaseSet ` u ) ( ( ( normCV ` u ) ` z ) <_ 1 /\ x = ( ( normCV ` w ) ` ( t ` z ) ) ) } , RR* , < ) ) )
end
