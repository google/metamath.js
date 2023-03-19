
axiom df-fwddif
  let vx: setvar x
  let vy: setvar y
  let vf: setvar f
  assert |- _/_\ = ( f e. ( CC ^pm CC ) |-> ( x e. { y e. dom f | ( y + 1 ) e. dom f } |-> ( ( f ` ( x + 1 ) ) - ( f ` x ) ) ) )
end
