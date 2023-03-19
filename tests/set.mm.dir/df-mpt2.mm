
axiom df-mpt2
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cA: class A
  let cB: class B
  let cC: class C
  assert |- ( x e. A , y e. B |-> C ) = { <. <. x , y >. , z >. | ( ( x e. A /\ y e. B ) /\ z = C ) }
end
