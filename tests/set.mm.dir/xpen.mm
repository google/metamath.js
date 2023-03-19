include "cen.mm"
include "wbr.mm"
include "wa.mm"
include "cxp.mm"
include "cdom.mm"
include "cvv.mm"
include "wcel.mm"
include "relen.mm"
include "brrelexi.mm"
include "endom.mm"
include "xpdom1g.mm"
include "syl2anr.mm"
include "brrelex2i.mm"
include "xpdom2g.mm"
include "syl2an.mm"
include "domtr.mm"
include "syl2anc.mm"
include "ensym.mm"
include "syl.mm"
include "sbth.mm"

theorem xpen
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D


  assert |- ( ( A ~~ B /\ C ~~ D ) -> ( A X. C ) ~~ ( B X. D ) )

  proof
    cA
    cB
    cen
    wbr
    #
    cC
    cD
    cen
    wbr
    #
    wa
    #
    cA
    cC
    cxp
    #
    cB
    cD
    cxp
    #
    cdom
    wbr
    #
    @4
    @3
    cdom
    wbr
    #
    @3
    @4
    cen
    wbr
    @2
    @3
    cB
    cC
    cxp
    #
    cdom
    wbr
    #
    @7
    @4
    cdom
    wbr
    #
    @5
    @1
    cC
    cvv
    wcel
    cA
    cB
    cdom
    wbr
    @8
    @0
    cC
    cD
    cen
    relen
    brrelexi
    cA
    cB
    endom
    cA
    cB
    cC
    cvv
    xpdom1g
    syl2anr
    @0
    cB
    cvv
    wcel
    cC
    cD
    cdom
    wbr
    @9
    @1
    cA
    cB
    cen
    relen
    brrelex2i
    cC
    cD
    endom
    cC
    cD
    cB
    cvv
    xpdom2g
    syl2an
    @3
    @7
    @4
    domtr
    syl2anc
    @2
    @4
    cA
    cD
    cxp
    #
    cdom
    wbr
    #
    @10
    @3
    cdom
    wbr
    #
    @6
    @1
    cD
    cvv
    wcel
    cB
    cA
    cdom
    wbr
    #
    @11
    @0
    cC
    cD
    cen
    relen
    brrelex2i
    @0
    cB
    cA
    cen
    wbr
    @13
    cA
    cB
    ensym
    cB
    cA
    endom
    syl
    cB
    cA
    cD
    cvv
    xpdom1g
    syl2anr
    @0
    cA
    cvv
    wcel
    cD
    cC
    cdom
    wbr
    #
    @12
    @1
    cA
    cB
    cen
    relen
    brrelexi
    @1
    cD
    cC
    cen
    wbr
    @14
    cC
    cD
    ensym
    cD
    cC
    endom
    syl
    cD
    cC
    cA
    cvv
    xpdom2g
    syl2an
    @4
    @10
    @3
    domtr
    syl2anc
    @3
    @4
    sbth
    syl2anc
end
