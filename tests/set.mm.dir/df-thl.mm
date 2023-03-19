
axiom df-thl
  let vh: setvar h
  assert |- toHL = ( h e. _V |-> ( ( toInc ` ( CSubSp ` h ) ) sSet <. ( oc ` ndx ) , ( ocv ` h ) >. ) )
end
