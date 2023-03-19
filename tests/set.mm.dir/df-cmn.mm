
axiom df-cmn
  let vg: setvar g
  let va: setvar a
  let vb: setvar b
  assert |- CMnd = { g e. Mnd | A. a e. ( Base ` g ) A. b e. ( Base ` g ) ( a ( +g ` g ) b ) = ( b ( +g ` g ) a ) }
end
