include "cv.mm"
include "wcel.mm"
include "biid.mm"
include "eqriv.mm"

theorem eqid
  param cA: class A
  let vx: setvar x


  assert |- A = A

  proof
    vx
    cA
    cA
    vx
    cv
    cA
    wcel
    biid
    eqriv
end
