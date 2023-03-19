
axiom df-seqom
  let vv: setvar v
  let vi: setvar i
  let cF: class F
  let cI: class I
  assert |- seqom ( F , I ) = ( rec ( ( i e. _om , v e. _V |-> <. suc i , ( i F v ) >. ) , <. (/) , ( _I ` I ) >. ) " _om )
end
