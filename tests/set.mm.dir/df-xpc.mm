
axiom df-xpc
  let vx: setvar x
  let vy: setvar y
  let vv: setvar v
  let vu: setvar u
  let vf: setvar f
  let vg: setvar g
  let vh: setvar h
  let vs: setvar s
  let vr: setvar r
  let vb: setvar b
  assert |- Xc. = ( r e. _V , s e. _V |-> [_ ( ( Base ` r ) X. ( Base ` s ) ) / b ]_ [_ ( u e. b , v e. b |-> ( ( ( 1st ` u ) ( Hom ` r ) ( 1st ` v ) ) X. ( ( 2nd ` u ) ( Hom ` s ) ( 2nd ` v ) ) ) ) / h ]_ { <. ( Base ` ndx ) , b >. , <. ( Hom ` ndx ) , h >. , <. ( comp ` ndx ) , ( x e. ( b X. b ) , y e. b |-> ( g e. ( ( 2nd ` x ) h y ) , f e. ( h ` x ) |-> <. ( ( 1st ` g ) ( <. ( 1st ` ( 1st ` x ) ) , ( 1st ` ( 2nd ` x ) ) >. ( comp ` r ) ( 1st ` y ) ) ( 1st ` f ) ) , ( ( 2nd ` g ) ( <. ( 2nd ` ( 1st ` x ) ) , ( 2nd ` ( 2nd ` x ) ) >. ( comp ` s ) ( 2nd ` y ) ) ( 2nd ` f ) ) >. ) ) >. } )
end
