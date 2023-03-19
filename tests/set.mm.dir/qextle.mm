include "cxr.mm"
include "wcel.mm"
include "wa.mm"
include "wceq.mm"
include "cv.mm"
include "cle.mm"
include "wbr.mm"
include "wb.mm"
include "cq.mm"
include "wral.mm"
include "breq2.mm"
include "ralrimivw.mm"
include "wne.mm"
include "wn.mm"
include "wrex.mm"
include "clt.mm"
include "wo.mm"
include "xrlttri2.mm"
include "qextltlem.mm"
include "simpr.mm"
include "reximi.mm"
include "syl6.mm"
include "wi.mm"
include "bicom.mm"
include "sylnib.mm"
include "ancoms.mm"
include "jaod.mm"
include "sylbid.mm"
include "rexnal.mm"
include "syl6ib.mm"
include "necon4ad.mm"
include "impbid2.mm"

theorem qextle
  let vx: setvar x
  let cA: class A
  let cB: class B

  disjoint A x
  disjoint B x
  assert |- ( ( A e. RR* /\ B e. RR* ) -> ( A = B <-> A. x e. QQ ( x <_ A <-> x <_ B ) ) )

  proof
    cA
    cxr
    wcel
    #
    cB
    cxr
    wcel
    #
    wa
    #
    cA
    cB
    wceq
    #
    vx
    cv
    #
    cA
    cle
    wbr
    #
    @4
    cB
    cle
    wbr
    #
    wb
    #
    vx
    cq
    wral
    #
    @3
    @7
    vx
    cq
    cA
    cB
    @4
    cle
    breq2
    ralrimivw
    @2
    @8
    cA
    cB
    @2
    cA
    cB
    wne
    #
    @7
    wn
    #
    vx
    cq
    wrex
    #
    @8
    wn
    @2
    @9
    cA
    cB
    clt
    wbr
    #
    cB
    cA
    clt
    wbr
    #
    wo
    @11
    cA
    cB
    xrlttri2
    @2
    @12
    @11
    @13
    @2
    @12
    @4
    cA
    clt
    wbr
    #
    @4
    cB
    clt
    wbr
    #
    wb
    wn
    #
    @10
    wa
    #
    vx
    cq
    wrex
    @11
    vx
    cA
    cB
    qextltlem
    @17
    @10
    vx
    cq
    @16
    @10
    simpr
    reximi
    syl6
    @1
    @0
    @13
    @11
    wi
    @1
    @0
    wa
    @13
    @15
    @14
    wb
    wn
    #
    @6
    @5
    wb
    #
    wn
    #
    wa
    #
    vx
    cq
    wrex
    @11
    vx
    cB
    cA
    qextltlem
    @21
    @10
    vx
    cq
    @21
    @19
    @7
    @18
    @20
    simpr
    @6
    @5
    bicom
    sylnib
    reximi
    syl6
    ancoms
    jaod
    sylbid
    @7
    vx
    cq
    rexnal
    syl6ib
    necon4ad
    impbid2
end
