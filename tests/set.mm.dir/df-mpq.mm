
axiom df-mpq
  let vx: setvar x
  let vy: setvar y
  assert |- .pQ = ( x e. ( N. X. N. ) , y e. ( N. X. N. ) |-> <. ( ( 1st ` x ) .N ( 1st ` y ) ) , ( ( 2nd ` x ) .N ( 2nd ` y ) ) >. )
end
