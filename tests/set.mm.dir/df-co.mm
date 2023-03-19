
axiom df-co
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cA: class A
  let cB: class B
  assert |- ( A o. B ) = { <. x , y >. | E. z ( x B z /\ z A y ) }
end
