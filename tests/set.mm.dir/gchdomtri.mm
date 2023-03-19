include "cgch.mm"
include "wcel.mm"
include "ccda.mm"
include "co.mm"
include "cen.mm"
include "wbr.mm"
include "cpw.mm"
include "cdom.mm"
include "w3a.mm"
include "cfn.mm"
include "wo.mm"
include "wa.mm"
include "wn.mm"
include "csdm.mm"
include "sdomdom.mm"
include "con3i.mm"
include "cvv.mm"
include "wb.mm"
include "reldom.mm"
include "brrelexi.mm"
include "3ad2ant3.mm"
include "fidomtri2.mm"
include "sylan.mm"
include "syl5ibr.mm"
include "orrd.mm"
include "simp1.mm"
include "adantr.mm"
include "simpr.mm"
include "cdadom3.mm"
include "syl2anc.mm"
include "cdalepw.mm"
include "3adant1.mm"
include "gchor.mm"
include "syl22anc.mm"
include "cdacomen.mm"
include "domentr.mm"
include "sylancl.mm"
include "domen2.mm"
include "syl5ibrcom.mm"
include "imp.mm"
include "olcd.mm"
include "simpl1.mm"
include "canth2g.mm"
include "3syl.mm"
include "simpl2.mm"
include "pwen.mm"
include "syl.mm"
include "enen2.mm"
include "adantl.mm"
include "mpbird.mm"
include "endom.mm"
include "pwcdadom.mm"
include "domtr.mm"
include "orcd.mm"
include "jaodan.mm"
include "syldan.mm"
include "pm2.61dan.mm"

theorem gchdomtri
  let cA: class A
  let cB: class B


  assert |- ( ( A e. GCH /\ ( A +c A ) ~~ A /\ B ~<_ ~P A ) -> ( A ~<_ B \/ B ~<_ A ) )

  proof
    cA
    cgch
    wcel
    #
    cA
    cA
    ccda
    co
    #
    cA
    cen
    wbr
    #
    cB
    cA
    cpw
    #
    cdom
    wbr
    #
    w3a
    #
    cA
    cfn
    wcel
    #
    cA
    cB
    cdom
    wbr
    #
    cB
    cA
    cdom
    wbr
    #
    wo
    #
    @5
    @6
    wa
    #
    @7
    @8
    @7
    wn
    @8
    @10
    cA
    cB
    csdm
    wbr
    #
    wn
    #
    @11
    @7
    cA
    cB
    sdomdom
    con3i
    @5
    cB
    cvv
    wcel
    #
    @6
    @8
    @12
    wb
    @4
    @0
    @13
    @2
    cB
    @3
    cdom
    reldom
    brrelexi
    3ad2ant3
    #
    cB
    cA
    cvv
    fidomtri2
    sylan
    syl5ibr
    orrd
    @5
    @6
    wn
    #
    cA
    cA
    cB
    ccda
    co
    #
    cen
    wbr
    #
    @16
    @3
    cen
    wbr
    #
    wo
    #
    @9
    @5
    @15
    wa
    @0
    @15
    cA
    @16
    cdom
    wbr
    #
    @16
    @3
    cdom
    wbr
    #
    @19
    @5
    @0
    @15
    @0
    @2
    @4
    simp1
    #
    adantr
    @5
    @15
    simpr
    @5
    @20
    @15
    @5
    @0
    @13
    @20
    @22
    @14
    cA
    cB
    cgch
    cvv
    cdadom3
    syl2anc
    adantr
    @5
    @21
    @15
    @2
    @4
    @21
    @0
    cA
    cB
    cdalepw
    3adant1
    adantr
    cA
    @16
    gchor
    syl22anc
    @5
    @17
    @9
    @18
    @5
    @17
    wa
    @8
    @7
    @5
    @17
    @8
    @5
    @8
    @17
    cB
    @16
    cdom
    wbr
    #
    @5
    cB
    cB
    cA
    ccda
    co
    #
    cdom
    wbr
    #
    @24
    @16
    cen
    wbr
    @23
    @5
    @13
    @0
    @25
    @14
    @22
    cB
    cA
    cvv
    cgch
    cdadom3
    syl2anc
    cB
    cA
    cdacomen
    cB
    @24
    @16
    domentr
    sylancl
    cA
    @16
    cB
    domen2
    syl5ibrcom
    imp
    olcd
    @5
    @18
    wa
    #
    @7
    @8
    @26
    cA
    @3
    cdom
    wbr
    #
    @3
    cB
    cdom
    wbr
    #
    @7
    @26
    @0
    cA
    @3
    csdm
    wbr
    @27
    @0
    @2
    @4
    @18
    simpl1
    cA
    cgch
    canth2g
    cA
    @3
    sdomdom
    3syl
    @26
    @1
    cpw
    #
    @16
    cen
    wbr
    #
    @29
    @16
    cdom
    wbr
    @28
    @26
    @30
    @29
    @3
    cen
    wbr
    #
    @26
    @2
    @31
    @0
    @2
    @4
    @18
    simpl2
    @1
    cA
    pwen
    syl
    @18
    @30
    @31
    wb
    @5
    @16
    @3
    @29
    enen2
    adantl
    mpbird
    @29
    @16
    endom
    cA
    cB
    pwcdadom
    3syl
    cA
    @3
    cB
    domtr
    syl2anc
    orcd
    jaodan
    syldan
    pm2.61dan
end
