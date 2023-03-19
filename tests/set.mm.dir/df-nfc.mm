
axiom df-nfc
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  assert |- ( F/_ x A <-> A. y F/ x y e. A )
end
