include "cvv.mm"
include "wcel.mm"
include "cdom.mm"
include "wbr.mm"
include "cxp.mm"
include "xpdom1g.mm"
include "mpan.mm"

theorem xpdom1
  let cA: class A
  let cB: class B
  let cC: class C
  assume xpdom1.2: |- C e. _V


  assert |- ( A ~<_ B -> ( A X. C ) ~<_ ( B X. C ) )

  proof
    cC
    cvv
    wcel
    cA
    cB
    cdom
    wbr
    cA
    cC
    cxp
    cB
    cC
    cxp
    cdom
    wbr
    xpdom1.2
    cA
    cB
    cC
    cvv
    xpdom1g
    mpan
end
