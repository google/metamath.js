
axiom df-symg
  let vx: setvar x
  let vf: setvar f
  let vg: setvar g
  let vh: setvar h
  let vb: setvar b
  assert |- SymGrp = ( x e. _V |-> [_ { h | h : x -1-1-onto-> x } / b ]_ { <. ( Base ` ndx ) , b >. , <. ( +g ` ndx ) , ( f e. b , g e. b |-> ( f o. g ) ) >. , <. ( TopSet ` ndx ) , ( Xt_ ` ( x X. { ~P x } ) ) >. } )
end
