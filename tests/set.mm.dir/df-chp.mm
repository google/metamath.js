
axiom df-chp
  let vx: setvar x
  let vn: setvar n
  assert |- psi = ( x e. RR |-> sum_ n e. ( 1 ... ( |_ ` x ) ) ( Lam ` n ) )
end
