
axiom df-ltpq
  let vx: setvar x
  let vy: setvar y
  assert |- <pQ = { <. x , y >. | ( ( x e. ( N. X. N. ) /\ y e. ( N. X. N. ) ) /\ ( ( 1st ` x ) .N ( 2nd ` y ) ) <N ( ( 1st ` y ) .N ( 2nd ` x ) ) ) }
end
