include "ccrd.mm"
include "cdm.mm"
include "wcel.mm"
include "com.mm"
include "cdom.mm"
include "wbr.mm"
include "w3a.mm"
include "cxp.mm"
include "cen.mm"
include "xpdom2g.mm"
include "3adant2.mm"
include "infxpidm2.mm"
include "3adant3.mm"
include "domentr.mm"
include "syl2anc.mm"

theorem infxpdom
  let cA: class A
  let cB: class B


  assert |- ( ( A e. dom card /\ _om ~<_ A /\ B ~<_ A ) -> ( A X. B ) ~<_ A )

  proof
    cA
    ccrd
    cdm
    #
    wcel
    #
    com
    cA
    cdom
    wbr
    #
    cB
    cA
    cdom
    wbr
    #
    w3a
    cA
    cB
    cxp
    #
    cA
    cA
    cxp
    #
    cdom
    wbr
    #
    @5
    cA
    cen
    wbr
    #
    @4
    cA
    cdom
    wbr
    @1
    @3
    @6
    @2
    cB
    cA
    cA
    @0
    xpdom2g
    3adant2
    @1
    @2
    @7
    @3
    cA
    infxpidm2
    3adant3
    @4
    @5
    cA
    domentr
    syl2anc
end
