
axiom df-bj-mgmhom
  let vx: setvar x
  let vy: setvar y
  let vv: setvar v
  let vu: setvar u
  let vf: setvar f
  assert |- -Mgm-> = ( x e. Mgm , y e. Mgm |-> { f e. ( ( Base ` x ) -Set-> ( Base ` y ) ) | A. u e. ( Base ` x ) A. v e. ( Base ` x ) ( f ` ( u ( +g ` x ) v ) ) = ( ( f ` u ) ( +g ` y ) ( f ` v ) ) } )
end
