include "cv.mm"
include "vex.mm"
include "elsn.mm"

theorem velsn
  let vx: setvar x
  let cA: class A


  assert |- ( x e. { A } <-> x = A )

  proof
    vx
    cv
    cA
    vx
    vex
    elsn
end
