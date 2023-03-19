
axiom df-gzf
  let vu: setvar u
  let vm: setvar m
  assert |- ZF = { m | ( ( Tr m /\ m |= AxExt /\ m |= AxPow ) /\ ( m |= AxUn /\ m |= AxReg /\ m |= AxInf ) /\ A. u e. ( Fmla ` _om ) m |= ( AxRep ` u ) ) }
end
