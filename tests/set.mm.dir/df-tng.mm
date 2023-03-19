
axiom df-tng
  let vf: setvar f
  let vg: setvar g
  assert |- toNrmGrp = ( g e. _V , f e. _V |-> ( ( g sSet <. ( dist ` ndx ) , ( f o. ( -g ` g ) ) >. ) sSet <. ( TopSet ` ndx ) , ( MetOpen ` ( f o. ( -g ` g ) ) ) >. ) )
end
