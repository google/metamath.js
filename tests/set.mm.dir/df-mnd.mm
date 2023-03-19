
axiom df-mnd
  let vx: setvar x
  let ve: setvar e
  let vg: setvar g
  let vp: setvar p
  let vb: setvar b
  assert |- Mnd = { g e. SGrp | [. ( Base ` g ) / b ]. [. ( +g ` g ) / p ]. E. e e. b A. x e. b ( ( e p x ) = x /\ ( x p e ) = x ) }
end
