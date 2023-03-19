include "com.mm"
include "cdom.mm"
include "wbr.mm"
include "wa.mm"
include "cxp.mm"
include "cen.mm"
include "cvv.mm"
include "wcel.mm"
include "ctex.mm"
include "adantl.mm"
include "simpl.mm"
include "xpdom1g.mm"
include "syl2anc.mm"
include "omex.mm"
include "xpdom2.mm"
include "domtr.mm"
include "xpomen.mm"
include "domentr.mm"
include "sylancl.mm"

theorem xpct
  let cA: class A
  let cB: class B


  assert |- ( ( A ~<_ _om /\ B ~<_ _om ) -> ( A X. B ) ~<_ _om )

  proof
    cA
    com
    cdom
    wbr
    #
    cB
    com
    cdom
    wbr
    #
    wa
    #
    cA
    cB
    cxp
    #
    com
    com
    cxp
    #
    cdom
    wbr
    #
    @4
    com
    cen
    wbr
    @3
    com
    cdom
    wbr
    @2
    @3
    com
    cB
    cxp
    #
    cdom
    wbr
    #
    @6
    @4
    cdom
    wbr
    #
    @5
    @2
    cB
    cvv
    wcel
    #
    @0
    @7
    @1
    @9
    @0
    cB
    ctex
    adantl
    @0
    @1
    simpl
    cA
    com
    cB
    cvv
    xpdom1g
    syl2anc
    @1
    @8
    @0
    cB
    com
    com
    omex
    xpdom2
    adantl
    @3
    @6
    @4
    domtr
    syl2anc
    xpomen
    @3
    @4
    com
    domentr
    sylancl
end
