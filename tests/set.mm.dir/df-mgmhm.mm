
axiom df-mgmhm
  let vx: setvar x
  let vy: setvar y
  let vt: setvar t
  let vf: setvar f
  let vs: setvar s
  assert |- MgmHom = ( s e. Mgm , t e. Mgm |-> { f e. ( ( Base ` t ) ^m ( Base ` s ) ) | A. x e. ( Base ` s ) A. y e. ( Base ` s ) ( f ` ( x ( +g ` s ) y ) ) = ( ( f ` x ) ( +g ` t ) ( f ` y ) ) } )
end
