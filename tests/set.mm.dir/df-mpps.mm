
axiom df-mpps
  let vt: setvar t
  let vh: setvar h
  let va: setvar a
  let vd: setvar d
  assert |- mPPSt = ( t e. _V |-> { <. <. d , h >. , a >. | ( <. d , h , a >. e. ( mPreSt ` t ) /\ a e. ( d ( mCls ` t ) h ) ) } )
end
