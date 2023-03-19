include "wcel.mm"
include "cdom.mm"
include "wbr.mm"
include "wa.mm"
include "cxp.mm"
include "cen.mm"
include "cvv.mm"
include "reldom.mm"
include "brrelexi.mm"
include "xpcomeng.mm"
include "ancoms.mm"
include "sylan2.mm"
include "xpdom2g.mm"
include "brrelex2i.mm"
include "domentr.mm"
include "syl2anc.mm"
include "endomtr.mm"

theorem xpdom1g
  let cA: class A
  let cB: class B
  let cC: class C
  let cV: class V
  let vx: setvar x
  let cW: class W


  assert |- ( ( C e. V /\ A ~<_ B ) -> ( A X. C ) ~<_ ( B X. C ) )

  proof
    cC
    cV
    wcel
    #
    cA
    cB
    cdom
    wbr
    #
    wa
    #
    cA
    cC
    cxp
    #
    cC
    cA
    cxp
    #
    cen
    wbr
    #
    @4
    cB
    cC
    cxp
    #
    cdom
    wbr
    #
    @3
    @6
    cdom
    wbr
    @1
    @0
    cA
    cvv
    wcel
    #
    @5
    cA
    cB
    cdom
    reldom
    brrelexi
    @8
    @0
    @5
    cA
    cC
    cvv
    cV
    xpcomeng
    ancoms
    sylan2
    @2
    @4
    cC
    cB
    cxp
    #
    cdom
    wbr
    @9
    @6
    cen
    wbr
    #
    @7
    cA
    cB
    cC
    cV
    xpdom2g
    @1
    @0
    cB
    cvv
    wcel
    @10
    cA
    cB
    cdom
    reldom
    brrelex2i
    cC
    cB
    cV
    cvv
    xpcomeng
    sylan2
    @4
    @9
    @6
    domentr
    syl2anc
    @3
    @4
    @6
    endomtr
    syl2anc
end
