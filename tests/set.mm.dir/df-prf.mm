
axiom df-prf
  let vx: setvar x
  let vy: setvar y
  let vf: setvar f
  let vg: setvar g
  let vh: setvar h
  let vb: setvar b
  assert |- pairF = ( f e. _V , g e. _V |-> [_ dom ( 1st ` f ) / b ]_ <. ( x e. b |-> <. ( ( 1st ` f ) ` x ) , ( ( 1st ` g ) ` x ) >. ) , ( x e. b , y e. b |-> ( h e. dom ( x ( 2nd ` f ) y ) |-> <. ( ( x ( 2nd ` f ) y ) ` h ) , ( ( x ( 2nd ` g ) y ) ` h ) >. ) ) >. )
end
