
axiom df-wun
  let vx: setvar x
  let vy: setvar y
  let vu: setvar u
  assert |- WUni = { u | ( Tr u /\ u =/= (/) /\ A. x e. u ( U. x e. u /\ ~P x e. u /\ A. y e. u { x , y } e. u ) ) }
end
