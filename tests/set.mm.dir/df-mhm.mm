
axiom df-mhm
  let vx: setvar x
  let vy: setvar y
  let vt: setvar t
  let vf: setvar f
  let vs: setvar s
  assert |- MndHom = ( s e. Mnd , t e. Mnd |-> { f e. ( ( Base ` t ) ^m ( Base ` s ) ) | ( A. x e. ( Base ` s ) A. y e. ( Base ` s ) ( f ` ( x ( +g ` s ) y ) ) = ( ( f ` x ) ( +g ` t ) ( f ` y ) ) /\ ( f ` ( 0g ` s ) ) = ( 0g ` t ) ) } )
end
