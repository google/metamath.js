
axiom df-scmat
  let vm: setvar m
  let vn: setvar n
  let vr: setvar r
  let va: setvar a
  let vc: setvar c
  assert |- ScMat = ( n e. Fin , r e. _V |-> [_ ( n Mat r ) / a ]_ { m e. ( Base ` a ) | E. c e. ( Base ` r ) m = ( c ( .s ` a ) ( 1r ` a ) ) } )
end
