
axiom df-gru
  let vx: setvar x
  let vy: setvar y
  let vu: setvar u
  assert |- Univ = { u | ( Tr u /\ A. x e. u ( ~P x e. u /\ A. y e. u { x , y } e. u /\ A. y e. ( u ^m x ) U. ran y e. u ) ) }
end
