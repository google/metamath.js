include "cv.mm"
include "vex.mm"
include "elpw.mm"

theorem selpw
  let vx: setvar x
  let cA: class A
  let cB: class B

  disjoint A x
  disjoint B x
  assert |- ( x e. ~P A <-> x C_ A )

  proof
    vx
    cv
    cA
    vx
    vex
    elpw
end
