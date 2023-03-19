
axiom df-dv
  let vx: setvar x
  let vz: setvar z
  let vf: setvar f
  let vs: setvar s
  assert |- _D = ( s e. ~P CC , f e. ( CC ^pm s ) |-> U_ x e. ( ( int ` ( ( TopOpen ` CCfld ) |`t s ) ) ` dom f ) ( { x } X. ( ( z e. ( dom f \ { x } ) |-> ( ( ( f ` z ) - ( f ` x ) ) / ( z - x ) ) ) limCC x ) ) )
end
