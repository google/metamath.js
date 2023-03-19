include "con0.mm"
include "wcel.mm"
include "com.mm"
include "wss.mm"
include "wa.mm"
include "cale.mm"
include "crn.mm"
include "ccrd.mm"
include "cfv.mm"
include "wceq.mm"
include "cv.mm"
include "cdom.mm"
include "wbr.mm"
include "wi.mm"
include "wral.mm"
include "wb.mm"
include "isinfcard.mm"
include "bicomi.mm"
include "baib.mm"
include "adantl.mm"
include "cdm.mm"
include "onenon.mm"
include "adantr.mm"
include "carddom2.mm"
include "syl2an.mm"
include "cardonle.mm"
include "sstr.mm"
include "expcom.mm"
include "syl.mm"
include "sylbird.mm"
include "sseq1.mm"
include "imbi2d.mm"
include "syl5ibcom.mm"
include "ralrimdva.mm"
include "cen.mm"
include "oncardid.mm"
include "ensym.mm"
include "endom.mm"
include "3syl.mm"
include "cardon.mm"
include "breq2.mm"
include "sseq2.mm"
include "imbi12d.mm"
include "rspcv.mm"
include "ax-mp.mm"
include "syl5com.mm"
include "biantrurd.mm"
include "eqss.mm"
include "syl6bbr.mm"
include "sylibd.mm"
include "impbid.mm"
include "bitrd.mm"

theorem alephinit
  let vx: setvar x
  let cA: class A

  disjoint A x
  assert |- ( ( A e. On /\ _om C_ A ) -> ( A e. ran aleph <-> A. x e. On ( A ~<_ x -> A C_ x ) ) )

  proof
    cA
    con0
    wcel
    #
    com
    cA
    wss
    #
    wa
    #
    cA
    cale
    crn
    wcel
    #
    cA
    ccrd
    cfv
    #
    cA
    wceq
    #
    cA
    vx
    cv
    #
    cdom
    wbr
    #
    cA
    @6
    wss
    #
    wi
    #
    vx
    con0
    wral
    #
    @1
    @3
    @5
    wb
    @0
    @3
    @1
    @5
    @1
    @5
    wa
    @3
    cA
    isinfcard
    bicomi
    baib
    adantl
    @2
    @5
    @10
    @2
    @5
    @9
    vx
    con0
    @2
    @6
    con0
    wcel
    #
    wa
    #
    @7
    @4
    @6
    wss
    #
    wi
    @5
    @9
    @12
    @7
    @4
    @6
    ccrd
    cfv
    #
    wss
    #
    @13
    @2
    cA
    ccrd
    cdm
    #
    wcel
    #
    @6
    @16
    wcel
    @15
    @7
    wb
    @11
    @0
    @17
    @1
    cA
    onenon
    adantr
    @6
    onenon
    cA
    @6
    carddom2
    syl2an
    @12
    @14
    @6
    wss
    #
    @15
    @13
    wi
    @11
    @18
    @2
    @6
    cardonle
    adantl
    @15
    @18
    @13
    @4
    @14
    @6
    sstr
    expcom
    syl
    sylbird
    @5
    @13
    @8
    @7
    @4
    cA
    @6
    sseq1
    imbi2d
    syl5ibcom
    ralrimdva
    @2
    @10
    cA
    @4
    wss
    #
    @5
    @2
    cA
    @4
    cdom
    wbr
    #
    @10
    @19
    @0
    @20
    @1
    @0
    @4
    cA
    cen
    wbr
    cA
    @4
    cen
    wbr
    @20
    cA
    oncardid
    @4
    cA
    ensym
    cA
    @4
    endom
    3syl
    adantr
    @4
    con0
    wcel
    @10
    @20
    @19
    wi
    #
    wi
    cA
    cardon
    @9
    @21
    vx
    @4
    con0
    @6
    @4
    wceq
    @7
    @20
    @8
    @19
    @6
    @4
    cA
    cdom
    breq2
    @6
    @4
    cA
    sseq2
    imbi12d
    rspcv
    ax-mp
    syl5com
    @2
    @19
    @4
    cA
    wss
    #
    @19
    wa
    @5
    @2
    @22
    @19
    @0
    @22
    @1
    cA
    cardonle
    adantr
    biantrurd
    @4
    cA
    eqss
    syl6bbr
    sylibd
    impbid
    bitrd
end
