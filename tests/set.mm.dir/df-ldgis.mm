
axiom df-ldgis
  let vx: setvar x
  let vi: setvar i
  let vj: setvar j
  let vk: setvar k
  let vr: setvar r
  assert |- ldgIdlSeq = ( r e. _V |-> ( i e. ( LIdeal ` ( Poly1 ` r ) ) |-> ( x e. NN0 |-> { j | E. k e. i ( ( ( deg1 ` r ) ` k ) <_ x /\ j = ( ( coe1 ` k ) ` x ) ) } ) ) )
end
