
axiom df-inito
  let vh: setvar h
  let va: setvar a
  let vb: setvar b
  let vc: setvar c
  assert |- InitO = ( c e. Cat |-> { a e. ( Base ` c ) | A. b e. ( Base ` c ) E! h h e. ( a ( Hom ` c ) b ) } )
end
