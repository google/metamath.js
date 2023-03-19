
axiom df-hcmp
  let vw: setvar w
  let vu: setvar u
  assert |- HCmp = { <. u , w >. | ( ( u e. U. ran UnifOn /\ w e. CUnifSp ) /\ ( ( UnifSt ` w ) |`t dom U. u ) = u /\ ( ( cls ` ( TopOpen ` w ) ) ` dom U. u ) = ( Base ` w ) ) }
end
