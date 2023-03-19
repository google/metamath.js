
axiom df-ghm
  let vx: setvar x
  let vy: setvar y
  let vw: setvar w
  let vt: setvar t
  let vg: setvar g
  let vs: setvar s
  assert |- GrpHom = ( s e. Grp , t e. Grp |-> { g | [. ( Base ` s ) / w ]. ( g : w --> ( Base ` t ) /\ A. x e. w A. y e. w ( g ` ( x ( +g ` s ) y ) ) = ( ( g ` x ) ( +g ` t ) ( g ` y ) ) ) } )
end
