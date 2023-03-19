include "cv.mm"
include "wcel.mm"
include "anidm.mm"
include "ineqri.mm"

theorem inidm
  let cA: class A
  let vx: setvar x


  assert |- ( A i^i A ) = A

  proof
    vx
    cA
    cA
    cA
    vx
    cv
    cA
    wcel
    anidm
    ineqri
end
