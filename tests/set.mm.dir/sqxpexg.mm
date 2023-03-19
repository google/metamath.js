include "wcel.mm"
include "cxp.mm"
include "cvv.mm"
include "xpexg.mm"
include "anidms.mm"

theorem sqxpexg
  let cA: class A
  let cV: class V


  assert |- ( A e. V -> ( A X. A ) e. _V )

  proof
    cA
    cV
    wcel
    cA
    cA
    cxp
    cvv
    wcel
    cA
    cA
    cV
    cV
    xpexg
    anidms
end
