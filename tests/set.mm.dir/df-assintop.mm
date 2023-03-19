
axiom df-assintop
  let vm: setvar m
  let vo: setvar o
  assert |- assIntOp = ( m e. _V |-> { o e. ( clIntOp ` m ) | o assLaw m } )
end
