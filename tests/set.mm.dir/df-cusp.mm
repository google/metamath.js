
axiom df-cusp
  let vw: setvar w
  let vc: setvar c
  assert |- CUnifSp = { w e. UnifSp | A. c e. ( Fil ` ( Base ` w ) ) ( c e. ( CauFilU ` ( UnifSt ` w ) ) -> ( ( TopOpen ` w ) fLim c ) =/= (/) ) }
end
