
axiom df-phtpy
  let vx: setvar x
  let vf: setvar f
  let vg: setvar g
  let vh: setvar h
  let vs: setvar s
  assert |- PHtpy = ( x e. Top |-> ( f e. ( II Cn x ) , g e. ( II Cn x ) |-> { h e. ( f ( II Htpy x ) g ) | A. s e. ( 0 [,] 1 ) ( ( 0 h s ) = ( f ` 0 ) /\ ( 1 h s ) = ( f ` 1 ) ) } ) )
end
