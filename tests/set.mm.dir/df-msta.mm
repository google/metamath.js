
axiom df-msta
  let vt: setvar t
  assert |- mStat = ( t e. _V |-> ran ( mStRed ` t ) )
end
