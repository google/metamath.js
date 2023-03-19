include "ccrd.mm"
include "cdm.mm"
include "wcel.mm"
include "com.mm"
include "cdom.mm"
include "wbr.mm"
include "wa.mm"
include "cxp.mm"
include "cfv.mm"
include "cen.mm"
include "cardid2.mm"
include "ensymd.mm"
include "xpen.mm"
include "syl2anc.mm"
include "adantr.mm"
include "con0.mm"
include "wss.mm"
include "cardon.mm"
include "cardom.mm"
include "wb.mm"
include "omelon.mm"
include "onenon.mm"
include "ax-mp.mm"
include "carddom2.mm"
include "mpan.mm"
include "biimpar.mm"
include "syl5eqssr.mm"
include "infxpen.mm"
include "sylancr.mm"
include "entr.mm"

theorem infxpidm2
  let cA: class A


  assert |- ( ( A e. dom card /\ _om ~<_ A ) -> ( A X. A ) ~~ A )

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
    wa
    #
    cA
    cA
    cxp
    #
    cA
    ccrd
    cfv
    #
    cen
    wbr
    #
    @5
    cA
    cen
    wbr
    #
    @4
    cA
    cen
    wbr
    @3
    @4
    @5
    @5
    cxp
    #
    cen
    wbr
    #
    @8
    @5
    cen
    wbr
    #
    @6
    @1
    @9
    @2
    @1
    cA
    @5
    cen
    wbr
    #
    @11
    @9
    @1
    @5
    cA
    cA
    cardid2
    #
    ensymd
    #
    @13
    cA
    @5
    cA
    @5
    xpen
    syl2anc
    adantr
    @3
    @5
    con0
    wcel
    com
    @5
    wss
    @10
    cA
    cardon
    @3
    com
    com
    ccrd
    cfv
    #
    @5
    cardom
    @1
    @14
    @5
    wss
    #
    @2
    com
    @0
    wcel
    #
    @1
    @15
    @2
    wb
    com
    con0
    wcel
    @16
    omelon
    com
    onenon
    ax-mp
    com
    cA
    carddom2
    mpan
    biimpar
    syl5eqssr
    @5
    infxpen
    sylancr
    @4
    @8
    @5
    entr
    syl2anc
    @1
    @7
    @2
    @12
    adantr
    @4
    @5
    cA
    entr
    syl2anc
end
