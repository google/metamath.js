
axiom df-iccp
  let vi: setvar i
  let vm: setvar m
  let vp: setvar p
  assert |- RePart = ( m e. NN |-> { p e. ( RR* ^m ( 0 ... m ) ) | A. i e. ( 0 ..^ m ) ( p ` i ) < ( p ` ( i + 1 ) ) } )
end
