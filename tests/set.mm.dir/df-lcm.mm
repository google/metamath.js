
axiom df-lcm
  let vx: setvar x
  let vy: setvar y
  let vn: setvar n
  assert |- lcm = ( x e. ZZ , y e. ZZ |-> if ( ( x = 0 \/ y = 0 ) , 0 , inf ( { n e. NN | ( x || n /\ y || n ) } , RR , < ) ) )
end
