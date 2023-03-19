
axiom df-isom
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let cR: class R
  let cS: class S
  let cH: class H
  assert |- ( H Isom R , S ( A , B ) <-> ( H : A -1-1-onto-> B /\ A. x e. A A. y e. A ( x R y <-> ( H ` x ) S ( H ` y ) ) ) )
end
