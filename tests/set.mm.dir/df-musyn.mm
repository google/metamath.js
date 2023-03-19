
axiom df-musyn
  let vv: setvar v
  let vt: setvar t
  assert |- mUSyn = ( t e. _V |-> ( v e. ( mUV ` t ) |-> <. ( ( mSyn ` t ) ` ( 1st ` v ) ) , ( 2nd ` v ) >. ) )
end
