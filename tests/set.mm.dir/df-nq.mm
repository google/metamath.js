
axiom df-nq
  let vx: setvar x
  let vy: setvar y
  assert |- Q. = { x e. ( N. X. N. ) | A. y e. ( N. X. N. ) ( x ~Q y -> -. ( 2nd ` y ) <N ( 2nd ` x ) ) }
end
