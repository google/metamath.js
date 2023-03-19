
axiom df-gcd
  let vx: setvar x
  let vy: setvar y
  let vn: setvar n
  assert |- gcd = ( x e. ZZ , y e. ZZ |-> if ( ( x = 0 /\ y = 0 ) , 0 , sup ( { n e. ZZ | ( n || x /\ n || y ) } , RR , < ) ) )
end
