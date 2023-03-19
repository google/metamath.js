include "wcel.mm"
include "cxp.mm"
include "cin.mm"
include "cvv.mm"
include "wa.mm"
include "inex1g.mm"
include "xpexg.mm"
include "inex2ALTV.mm"
include "syl.mm"
include "jaoi.mm"

theorem inxpex
  let cA: class A
  let cB: class B
  let cR: class R
  let cU: class U
  let cV: class V
  let cW: class W


  assert |- ( ( R e. W \/ ( A e. U /\ B e. V ) ) -> ( R i^i ( A X. B ) ) e. _V )

  proof
    cR
    cW
    wcel
    cR
    cA
    cB
    cxp
    #
    cin
    cvv
    wcel
    #
    cA
    cU
    wcel
    cB
    cV
    wcel
    wa
    #
    cR
    @0
    cW
    inex1g
    @2
    @0
    cvv
    wcel
    @1
    cA
    cB
    cU
    cV
    xpexg
    @0
    cR
    cvv
    inex2ALTV
    syl
    jaoi
end
