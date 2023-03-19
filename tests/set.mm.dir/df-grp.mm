
axiom df-grp
  let vg: setvar g
  let vm: setvar m
  let va: setvar a
  assert |- Grp = { g e. Mnd | A. a e. ( Base ` g ) E. m e. ( Base ` g ) ( m ( +g ` g ) a ) = ( 0g ` g ) }
end
