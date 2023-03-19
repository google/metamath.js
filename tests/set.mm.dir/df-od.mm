
axiom df-od
  let vx: setvar x
  let vg: setvar g
  let vi: setvar i
  let vn: setvar n
  assert |- od = ( g e. _V |-> ( x e. ( Base ` g ) |-> [_ { n e. NN | ( n ( .g ` g ) x ) = ( 0g ` g ) } / i ]_ if ( i = (/) , 0 , inf ( i , RR , < ) ) ) )
end
