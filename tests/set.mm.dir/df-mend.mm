
axiom df-mend
  let vx: setvar x
  let vy: setvar y
  let vm: setvar m
  let vb: setvar b
  assert |- MEndo = ( m e. _V |-> [_ ( m LMHom m ) / b ]_ ( { <. ( Base ` ndx ) , b >. , <. ( +g ` ndx ) , ( x e. b , y e. b |-> ( x oF ( +g ` m ) y ) ) >. , <. ( .r ` ndx ) , ( x e. b , y e. b |-> ( x o. y ) ) >. } u. { <. ( Scalar ` ndx ) , ( Scalar ` m ) >. , <. ( .s ` ndx ) , ( x e. ( Base ` ( Scalar ` m ) ) , y e. b |-> ( ( ( Base ` m ) X. { x } ) oF ( .s ` m ) y ) ) >. } ) )
end
