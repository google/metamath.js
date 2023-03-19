include "ccda.mm"
include "co.mm"
include "cen.mm"
include "wbr.mm"
include "cpw.mm"
include "cdom.mm"
include "wa.mm"
include "c0.mm"
include "wceq.mm"
include "oveq1.mm"
include "breq1d.mm"
include "wne.mm"
include "c1o.mm"
include "cvv.mm"
include "wcel.mm"
include "csdm.mm"
include "relen.mm"
include "brrelex2i.mm"
include "adantr.mm"
include "canth2g.mm"
include "sdomdom.mm"
include "3syl.mm"
include "simpr.mm"
include "cdadom1.mm"
include "cdadom2.mm"
include "domtr.mm"
include "syl2an.mm"
include "syl2anc.mm"
include "pwcda1.mm"
include "syl.mm"
include "domentr.mm"
include "wb.mm"
include "0sdomg.mm"
include "biimpar.mm"
include "0sdom1dom.mm"
include "sylib.mm"
include "simpll.mm"
include "pwdom.mm"
include "cdacomen.mm"
include "reldom.mm"
include "brrelexi.mm"
include "adantl.mm"
include "cda0en.mm"
include "domen1.mm"
include "mpbird.mm"
include "endomtr.mm"
include "sylancr.mm"
include "pm2.61ne.mm"

theorem cdalepw
  let cA: class A
  let cB: class B


  assert |- ( ( ( A +c A ) ~~ A /\ B ~<_ ~P A ) -> ( A +c B ) ~<_ ~P A )

  proof
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
    wa
    #
    cA
    cB
    ccda
    co
    #
    @2
    cdom
    wbr
    #
    c0
    cB
    ccda
    co
    #
    @2
    cdom
    wbr
    #
    cA
    c0
    cA
    c0
    wceq
    @5
    @7
    @2
    cdom
    cA
    c0
    cB
    ccda
    oveq1
    breq1d
    @4
    cA
    c0
    wne
    #
    wa
    #
    @5
    cA
    c1o
    ccda
    co
    #
    cpw
    #
    cdom
    wbr
    #
    @12
    @2
    cdom
    wbr
    #
    @6
    @4
    @13
    @9
    @4
    @5
    @2
    @2
    ccda
    co
    #
    cdom
    wbr
    #
    @15
    @12
    cen
    wbr
    #
    @13
    @4
    cA
    @2
    cdom
    wbr
    #
    @3
    @16
    @4
    cA
    cvv
    wcel
    #
    cA
    @2
    csdm
    wbr
    @18
    @1
    @19
    @3
    @0
    cA
    cen
    relen
    brrelex2i
    adantr
    #
    cA
    cvv
    canth2g
    cA
    @2
    sdomdom
    3syl
    @1
    @3
    simpr
    #
    @18
    @5
    @2
    cB
    ccda
    co
    #
    cdom
    wbr
    @22
    @15
    cdom
    wbr
    @16
    @3
    cA
    @2
    cB
    cdadom1
    cB
    @2
    @2
    cdadom2
    @5
    @22
    @15
    domtr
    syl2an
    syl2anc
    @4
    @19
    @17
    @20
    cA
    cvv
    pwcda1
    syl
    @5
    @15
    @12
    domentr
    syl2anc
    adantr
    @10
    @11
    cA
    cdom
    wbr
    #
    @14
    @10
    @11
    @0
    cdom
    wbr
    #
    @1
    @23
    @10
    c1o
    cA
    cdom
    wbr
    #
    @24
    @10
    c0
    cA
    csdm
    wbr
    #
    @25
    @4
    @26
    @9
    @4
    @19
    @26
    @9
    wb
    @20
    cA
    cvv
    0sdomg
    syl
    biimpar
    cA
    0sdom1dom
    sylib
    c1o
    cA
    cA
    cdadom2
    syl
    @1
    @3
    @9
    simpll
    @11
    @0
    cA
    domentr
    syl2anc
    @11
    cA
    pwdom
    syl
    @5
    @12
    @2
    domtr
    syl2anc
    @4
    @7
    cB
    c0
    ccda
    co
    #
    cen
    wbr
    @27
    @2
    cdom
    wbr
    #
    @8
    c0
    cB
    cdacomen
    @4
    @28
    @3
    @21
    @4
    cB
    cvv
    wcel
    #
    @27
    cB
    cen
    wbr
    @28
    @3
    wb
    @3
    @29
    @1
    cB
    @2
    cdom
    reldom
    brrelexi
    adantl
    cB
    cvv
    cda0en
    @27
    cB
    @2
    domen1
    3syl
    mpbird
    @7
    @27
    @2
    endomtr
    sylancr
    pm2.61ne
end
