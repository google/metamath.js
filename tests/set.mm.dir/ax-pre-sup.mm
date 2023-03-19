
axiom ax-pre-sup
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cA: class A
  assert |- ( ( A C_ RR /\ A =/= (/) /\ E. x e. RR A. y e. A y <RR x ) -> E. x e. RR ( A. y e. A -. x <RR y /\ A. y e. RR ( y <RR x -> E. z e. A y <RR z ) ) )
end
