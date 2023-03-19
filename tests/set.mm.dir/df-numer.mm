
axiom df-numer
  let vx: setvar x
  let vy: setvar y
  assert |- numer = ( y e. QQ |-> ( 1st ` ( iota_ x e. ( ZZ X. NN ) ( ( ( 1st ` x ) gcd ( 2nd ` x ) ) = 1 /\ y = ( ( 1st ` x ) / ( 2nd ` x ) ) ) ) ) )
end
