
axiom df-rrn
  let vx: setvar x
  let vy: setvar y
  let vi: setvar i
  let vk: setvar k
  assert |- Rn = ( i e. Fin |-> ( x e. ( RR ^m i ) , y e. ( RR ^m i ) |-> ( sqrt ` sum_ k e. i ( ( ( x ` k ) - ( y ` k ) ) ^ 2 ) ) ) )
end
