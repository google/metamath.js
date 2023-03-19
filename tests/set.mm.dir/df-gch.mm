
axiom df-gch
  let vx: setvar x
  let vy: setvar y
  assert |- GCH = ( Fin u. { x | A. y -. ( x ~< y /\ y ~< ~P x ) } )
end
