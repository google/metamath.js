
axiom df-algind
  let vw: setvar w
  let vv: setvar v
  let vf: setvar f
  let vk: setvar k
  assert |- AlgInd = ( w e. _V , k e. ~P ( Base ` w ) |-> { v e. ~P ( Base ` w ) | Fun `' ( f e. ( Base ` ( v mPoly ( w |`s k ) ) ) |-> ( ( ( ( v evalSub w ) ` k ) ` f ) ` ( _I |` v ) ) ) } )
end
