include "ccrd.mm"
include "cdm.mm"
include "wcel.mm"
include "com.mm"
include "cdom.mm"
include "wbr.mm"
include "w3a.mm"
include "ccda.mm"
include "co.mm"
include "cen.mm"
include "cxp.mm"
include "c2o.mm"
include "cdadom2.mm"
include "3ad2ant3.mm"
include "wceq.mm"
include "simp1.mm"
include "xp2cda.mm"
include "syl.mm"
include "breqtrrd.mm"
include "csdm.mm"
include "2onn.mm"
include "nnsdom.mm"
include "sdomdom.mm"
include "mp2b.mm"
include "simp2.mm"
include "domtr.mm"
include "sylancr.mm"
include "xpdom2g.mm"
include "syl2anc.mm"
include "infxpidm2.mm"
include "3adant3.mm"
include "domentr.mm"
include "cvv.mm"
include "reldom.mm"
include "brrelexi.mm"
include "cdadom3.mm"
include "sbth.mm"

theorem infcdaabs
  let cA: class A
  let cB: class B


  assert |- ( ( A e. dom card /\ _om ~<_ A /\ B ~<_ A ) -> ( A +c B ) ~~ A )

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
    #
    cA
    cB
    ccda
    co
    #
    cA
    cdom
    wbr
    #
    cA
    @5
    cdom
    wbr
    #
    @5
    cA
    cen
    wbr
    @4
    @5
    cA
    cA
    cxp
    #
    cdom
    wbr
    #
    @8
    cA
    cen
    wbr
    #
    @6
    @4
    @5
    cA
    c2o
    cxp
    #
    cdom
    wbr
    @11
    @8
    cdom
    wbr
    #
    @9
    @4
    @5
    cA
    cA
    ccda
    co
    #
    @11
    cdom
    @3
    @1
    @5
    @13
    cdom
    wbr
    @2
    cB
    cA
    cA
    cdadom2
    3ad2ant3
    @4
    @1
    @11
    @13
    wceq
    @1
    @2
    @3
    simp1
    #
    cA
    @0
    xp2cda
    syl
    breqtrrd
    @4
    @1
    c2o
    cA
    cdom
    wbr
    #
    @12
    @14
    @4
    c2o
    com
    cdom
    wbr
    #
    @2
    @15
    c2o
    com
    wcel
    c2o
    com
    csdm
    wbr
    @16
    2onn
    c2o
    nnsdom
    c2o
    com
    sdomdom
    mp2b
    @1
    @2
    @3
    simp2
    c2o
    com
    cA
    domtr
    sylancr
    c2o
    cA
    cA
    @0
    xpdom2g
    syl2anc
    @5
    @11
    @8
    domtr
    syl2anc
    @1
    @2
    @10
    @3
    cA
    infxpidm2
    3adant3
    @5
    @8
    cA
    domentr
    syl2anc
    @4
    @1
    cB
    cvv
    wcel
    #
    @7
    @14
    @3
    @1
    @17
    @2
    cB
    cA
    cdom
    reldom
    brrelexi
    3ad2ant3
    cA
    cB
    @0
    cvv
    cdadom3
    syl2anc
    @5
    cA
    sbth
    syl2anc
end
