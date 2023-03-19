
axiom df-hof
  let vx: setvar x
  let vy: setvar y
  let vf: setvar f
  let vg: setvar g
  let vh: setvar h
  let vb: setvar b
  let vc: setvar c
  assert |- HomF = ( c e. Cat |-> <. ( Homf ` c ) , [_ ( Base ` c ) / b ]_ ( x e. ( b X. b ) , y e. ( b X. b ) |-> ( f e. ( ( 1st ` y ) ( Hom ` c ) ( 1st ` x ) ) , g e. ( ( 2nd ` x ) ( Hom ` c ) ( 2nd ` y ) ) |-> ( h e. ( ( Hom ` c ) ` x ) |-> ( ( g ( x ( comp ` c ) ( 2nd ` y ) ) h ) ( <. ( 1st ` y ) , ( 1st ` x ) >. ( comp ` c ) ( 2nd ` y ) ) f ) ) ) ) >. )
end
