
axiom df-dib
  let vx: setvar x
  let vw: setvar w
  let vf: setvar f
  let vk: setvar k
  assert |- DIsoB = ( k e. _V |-> ( w e. ( LHyp ` k ) |-> ( x e. dom ( ( DIsoA ` k ) ` w ) |-> ( ( ( ( DIsoA ` k ) ` w ) ` x ) X. { ( f e. ( ( LTrn ` k ) ` w ) |-> ( _I |` ( Base ` k ) ) ) } ) ) ) )
end
