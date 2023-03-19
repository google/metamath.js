
axiom df-logbALT
  let vx: setvar x
  let vb: setvar b
  assert |- log_ = ( b e. ( CC \ { 0 , 1 } ) |-> ( x e. ( CC \ { 0 } ) |-> ( ( log ` x ) / ( log ` b ) ) ) )
end
