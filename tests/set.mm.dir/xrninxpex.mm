include "wcel.mm"
include "cxrn.mm"
include "cxp.mm"
include "cin.mm"
include "cvv.mm"
include "wa.mm"
include "xpexg.mm"
include "inxpex.mm"
include "olcs.mm"
include "sylan2.mm"
include "3impb.mm"

theorem xrninxpex
  let cA: class A
  let cB: class B
  let cC: class C
  let cR: class R
  let cS: class S
  let cV: class V
  let cW: class W
  let cX: class X


  assert |- ( ( A e. V /\ B e. W /\ C e. X ) -> ( ( R |X. S ) i^i ( A X. ( B X. C ) ) ) e. _V )

  proof
    cA
    cV
    wcel
    #
    cB
    cW
    wcel
    #
    cC
    cX
    wcel
    #
    cR
    cS
    cxrn
    #
    cA
    cB
    cC
    cxp
    #
    cxp
    cin
    cvv
    wcel
    #
    @1
    @2
    wa
    @0
    @4
    cvv
    wcel
    #
    @5
    cB
    cC
    cW
    cX
    xpexg
    @3
    cvv
    wcel
    @0
    @6
    wa
    @5
    cA
    @4
    @3
    cV
    cvv
    cvv
    inxpex
    olcs
    sylan2
    3impb
end
