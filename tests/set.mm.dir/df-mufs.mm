
axiom df-mufs
  let vt: setvar t
  assert |- mUFS = { t e. mGFS | Fun ( mST ` t ) }
end
