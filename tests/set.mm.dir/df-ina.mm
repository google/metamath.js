
axiom df-ina
  let vx: setvar x
  let vy: setvar y
  assert |- Inacc = { x | ( x =/= (/) /\ ( cf ` x ) = x /\ A. y e. x ~P y ~< x ) }
end
