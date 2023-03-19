
axiom df-mst
  let vt: setvar t
  assert |- mST = ( t e. _V |-> ( ( (/) ( mTree ` t ) (/) ) |` ( ( mEx ` t ) |` ( mVT ` t ) ) ) )
end
