
axiom df-dilN
  let vx: setvar x
  let vf: setvar f
  let vk: setvar k
  let vd: setvar d
  assert |- Dil = ( k e. _V |-> ( d e. ( Atoms ` k ) |-> { f e. ( PAut ` k ) | A. x e. ( PSubSp ` k ) ( x C_ ( ( WAtoms ` k ) ` d ) -> ( f ` x ) = x ) } ) )
end
