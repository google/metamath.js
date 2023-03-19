
axiom df-rlim
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vw: setvar w
  let vf: setvar f
  assert |- ~~>r = { <. f , x >. | ( ( f e. ( CC ^pm RR ) /\ x e. CC ) /\ A. y e. RR+ E. z e. RR A. w e. dom f ( z <_ w -> ( abs ` ( ( f ` w ) - x ) ) < y ) ) }
end
