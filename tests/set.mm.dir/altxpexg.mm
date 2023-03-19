include "wcel.mm"
include "wa.mm"
include "caltxp.mm"
include "cpw.mm"
include "cun.mm"
include "wss.mm"
include "cvv.mm"
include "altxpsspw.mm"
include "pwexg.mm"
include "unexg.mm"
include "sylan2.mm"
include "3syl.mm"
include "ssexg.mm"
include "sylancr.mm"

theorem altxpexg
  let cA: class A
  let cB: class B
  let cV: class V
  let cW: class W


  assert |- ( ( A e. V /\ B e. W ) -> ( A XX. B ) e. _V )

  proof
    cA
    cV
    wcel
    #
    cB
    cW
    wcel
    #
    wa
    #
    cA
    cB
    caltxp
    #
    cA
    cB
    cpw
    #
    cun
    #
    cpw
    #
    cpw
    #
    wss
    @7
    cvv
    wcel
    #
    @3
    cvv
    wcel
    cA
    cB
    altxpsspw
    @2
    @5
    cvv
    wcel
    #
    @6
    cvv
    wcel
    @8
    @1
    @0
    @4
    cvv
    wcel
    @9
    cB
    cW
    pwexg
    cA
    @4
    cV
    cvv
    unexg
    sylan2
    @5
    cvv
    pwexg
    @6
    cvv
    pwexg
    3syl
    @3
    @7
    cvv
    ssexg
    sylancr
end
