include "wcel.mm"
include "wa.mm"
include "cxp.mm"
include "cun.mm"
include "cpw.mm"
include "wss.mm"
include "cvv.mm"
include "xpsspw.mm"
include "unexg.mm"
include "pwexg.mm"
include "3syl.mm"
include "ssexg.mm"
include "sylancr.mm"

theorem xpexg
  let cA: class A
  let cB: class B
  let cV: class V
  let cW: class W


  assert |- ( ( A e. V /\ B e. W ) -> ( A X. B ) e. _V )

  proof
    cA
    cV
    wcel
    cB
    cW
    wcel
    wa
    #
    cA
    cB
    cxp
    #
    cA
    cB
    cun
    #
    cpw
    #
    cpw
    #
    wss
    @4
    cvv
    wcel
    #
    @1
    cvv
    wcel
    cA
    cB
    xpsspw
    @0
    @2
    cvv
    wcel
    @3
    cvv
    wcel
    @5
    cA
    cB
    cV
    cW
    unexg
    @2
    cvv
    pwexg
    @3
    cvv
    pwexg
    3syl
    @1
    @4
    cvv
    ssexg
    sylancr
end
