
axiom df-mwgfs
  let vt: setvar t
  let vh: setvar h
  let vs: setvar s
  let va: setvar a
  let vd: setvar d
  assert |- mWGFS = { t e. mFS | A. d A. h A. a ( ( <. d , h , a >. e. ( mAx ` t ) /\ ( 1st ` a ) e. ( mVT ` t ) ) -> E. s e. ran ( mSubst ` t ) a e. ( s " ( mSA ` t ) ) ) }
end
