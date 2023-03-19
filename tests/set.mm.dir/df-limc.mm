
axiom df-limc
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vf: setvar f
  let vj: setvar j
  assert |- limCC = ( f e. ( CC ^pm CC ) , x e. CC |-> { y | [. ( TopOpen ` CCfld ) / j ]. ( z e. ( dom f u. { x } ) |-> if ( z = x , y , ( f ` z ) ) ) e. ( ( ( j |`t ( dom f u. { x } ) ) CnP j ) ` x ) } )
end
