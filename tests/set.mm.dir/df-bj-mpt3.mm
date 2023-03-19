
axiom df-bj-mpt3
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vt: setvar t
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let vs: setvar s
  assert |- ( x e. A , y e. B , z e. C |-> D ) = { <. s , t >. | E. x e. A E. y e. B E. z e. C ( s = <. x , y , z >. /\ t = D ) }
end
