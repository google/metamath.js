include "cvv.mm"
include "cv.mm"
include "elex.mm"
include "ssriv.mm"

theorem ssv
  let cA: class A
  let vx: setvar x


  assert |- A C_ _V

  proof
    vx
    cA
    cvv
    vx
    cv
    cA
    elex
    ssriv
end
