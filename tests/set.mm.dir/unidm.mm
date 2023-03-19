include "cv.mm"
include "wcel.mm"
include "oridm.mm"
include "uneqri.mm"

theorem unidm
  let cA: class A
  let vx: setvar x


  assert |- ( A u. A ) = A

  proof
    vx
    cA
    cA
    cA
    vx
    cv
    cA
    wcel
    oridm
    uneqri
end
