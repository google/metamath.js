include "wcel.mm"
include "cxp.mm"
include "cvv.mm"
include "xpexg.mm"
include "ex.mm"

theorem bj-xpexg2
  let cA: class A
  let cB: class B
  let cV: class V
  let cW: class W


  assert |- ( A e. V -> ( B e. W -> ( A X. B ) e. _V ) )

  proof
    cA
    cV
    wcel
    cB
    cW
    wcel
    cA
    cB
    cxp
    cvv
    wcel
    cA
    cB
    cV
    cW
    xpexg
    ex
end
