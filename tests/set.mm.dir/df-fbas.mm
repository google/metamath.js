
axiom df-fbas
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vw: setvar w
  assert |- fBas = ( w e. _V |-> { x e. ~P ~P w | ( x =/= (/) /\ (/) e/ x /\ A. y e. x A. z e. x ( x i^i ~P ( y i^i z ) ) =/= (/) ) } )
end
