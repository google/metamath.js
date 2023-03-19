
axiom df-locfin
  let vx: setvar x
  let vy: setvar y
  let vn: setvar n
  let vs: setvar s
  let vp: setvar p
  assert |- LocFin = ( x e. Top |-> { y | ( U. x = U. y /\ A. p e. U. x E. n e. x ( p e. n /\ { s e. y | ( s i^i n ) =/= (/) } e. Fin ) ) } )
end
