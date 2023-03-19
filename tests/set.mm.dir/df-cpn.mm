
axiom df-cpn
  let vx: setvar x
  let vf: setvar f
  let vs: setvar s
  assert |- C^n = ( s e. ~P CC |-> ( x e. NN0 |-> { f e. ( CC ^pm s ) | ( ( s Dn f ) ` x ) e. ( dom f -cn-> CC ) } ) )
end
