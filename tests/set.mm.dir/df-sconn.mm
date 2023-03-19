
axiom df-sconn
  let vf: setvar f
  let vj: setvar j
  assert |- SConn = { j e. PConn | A. f e. ( II Cn j ) ( ( f ` 0 ) = ( f ` 1 ) -> f ( ~=ph ` j ) ( ( 0 [,] 1 ) X. { ( f ` 0 ) } ) ) }
end
