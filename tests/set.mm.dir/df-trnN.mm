
axiom df-trnN
  let vf: setvar f
  let vk: setvar k
  let vr: setvar r
  let vq: setvar q
  let vd: setvar d
  assert |- Trn = ( k e. _V |-> ( d e. ( Atoms ` k ) |-> { f e. ( ( Dil ` k ) ` d ) | A. q e. ( ( WAtoms ` k ) ` d ) A. r e. ( ( WAtoms ` k ) ` d ) ( ( q ( +P ` k ) ( f ` q ) ) i^i ( ( _|_P ` k ) ` { d } ) ) = ( ( r ( +P ` k ) ( f ` r ) ) i^i ( ( _|_P ` k ) ` { d } ) ) } ) )
end
