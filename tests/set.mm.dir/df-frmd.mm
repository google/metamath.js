
axiom df-frmd
  let vi: setvar i
  assert |- freeMnd = ( i e. _V |-> { <. ( Base ` ndx ) , Word i >. , <. ( +g ` ndx ) , ( ++ |` ( Word i X. Word i ) ) >. } )
end
