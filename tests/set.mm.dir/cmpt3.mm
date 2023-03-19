
axiom cmpt3
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  assert class ( x e. A , y e. B , z e. C |-> D )
end
