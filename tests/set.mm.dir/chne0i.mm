include "chshii.mm"
include "shne0i.mm"

theorem chne0i
  let vx: setvar x
  let cA: class A
  let vy: setvar y
  assume ch0le.1: |- A e. CH

  disjoint A x
  disjoint x y
  disjoint A y
  assert |- ( A =/= 0H <-> E. x e. A x =/= 0h )

  proof
    vx
    cA
    cA
    ch0le.1
    chshii
    shne0i
end
