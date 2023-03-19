
axiom df-termo
  let vh: setvar h
  let va: setvar a
  let vb: setvar b
  let vc: setvar c
  assert |- TermO = ( c e. Cat |-> { a e. ( Base ` c ) | A. b e. ( Base ` c ) E! h h e. ( b ( Hom ` c ) a ) } )
end
