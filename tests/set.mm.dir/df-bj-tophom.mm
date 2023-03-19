
axiom df-bj-tophom
  let vx: setvar x
  let vy: setvar y
  let vu: setvar u
  let vf: setvar f
  assert |- -Top-> = ( x e. TopSp , y e. TopSp |-> { f e. ( ( Base ` x ) -Set-> ( Base ` y ) ) | A. u e. ( TopOpen ` y ) ( `' f " u ) e. ( TopOpen ` x ) } )
end
