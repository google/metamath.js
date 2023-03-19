

axiom df-nfc
  param vx: setvar x
  param vy: setvar y
  param cA: class A
  assert |- ( F/_ x A <-> A. y F/ x y e. A )
end
