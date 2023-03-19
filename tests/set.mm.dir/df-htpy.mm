
axiom df-htpy
  let vx: setvar x
  let vy: setvar y
  let vf: setvar f
  let vg: setvar g
  let vh: setvar h
  let vs: setvar s
  assert |- Htpy = ( x e. Top , y e. Top |-> ( f e. ( x Cn y ) , g e. ( x Cn y ) |-> { h e. ( ( x tX II ) Cn y ) | A. s e. U. x ( ( s h 0 ) = ( f ` s ) /\ ( s h 1 ) = ( g ` s ) ) } ) )
end
