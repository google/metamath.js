
axiom df-phi
  let vx: setvar x
  let vn: setvar n
  assert |- phi = ( n e. NN |-> ( # ` { x e. ( 1 ... n ) | ( x gcd n ) = 1 } ) )
end
