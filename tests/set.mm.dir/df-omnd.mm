
axiom df-omnd
  let vv: setvar v
  let vg: setvar g
  let vp: setvar p
  let va: setvar a
  let vb: setvar b
  let vc: setvar c
  let vl: setvar l
  assert |- oMnd = { g e. Mnd | [. ( Base ` g ) / v ]. [. ( +g ` g ) / p ]. [. ( le ` g ) / l ]. ( g e. Toset /\ A. a e. v A. b e. v A. c e. v ( a l b -> ( a p c ) l ( b p c ) ) ) }
end
