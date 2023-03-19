
axiom df-logb
  let vx: setvar x
  let vy: setvar y
  assert |- logb = ( x e. ( CC \ { 0 , 1 } ) , y e. ( CC \ { 0 } ) |-> ( ( log ` y ) / ( log ` x ) ) )
end
