
axiom df-ixp
  let vx: setvar x
  let cA: class A
  let cB: class B
  let vf: setvar f
  assert |- X_ x e. A B = { f | ( f Fn { x | x e. A } /\ A. x e. A ( f ` x ) e. B ) }
end
