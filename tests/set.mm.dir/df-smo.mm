
axiom df-smo
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  assert |- ( Smo A <-> ( A : dom A --> On /\ Ord dom A /\ A. x e. dom A A. y e. dom A ( x e. y -> ( A ` x ) e. ( A ` y ) ) ) )
end
