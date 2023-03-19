
axiom df-denom
  let vx: setvar x
  let vy: setvar y
  assert |- denom = ( y e. QQ |-> ( 2nd ` ( iota_ x e. ( ZZ X. NN ) ( ( ( 1st ` x ) gcd ( 2nd ` x ) ) = 1 /\ y = ( ( 1st ` x ) / ( 2nd ` x ) ) ) ) ) )
end
