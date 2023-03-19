include "cale.mm"
include "cfv.mm"
include "csdm.mm"
include "wbr.mm"
include "csuc.mm"
include "wa.mm"
include "ccrd.mm"
include "wcel.mm"
include "wceq.mm"
include "wn.mm"
include "cardidm.mm"
include "alephnbtwn.mm"
include "ax-mp.mm"
include "cen.mm"
include "cdm.mm"
include "con0.mm"
include "cdom.mm"
include "alephon.mm"
include "sdomdom.mm"
include "ondomen.mm"
include "sylancr.mm"
include "cardid2.mm"
include "syl.mm"
include "ensymd.mm"
include "sdomentr.mm"
include "sylan2.mm"
include "wb.mm"
include "cardon.mm"
include "onenon.mm"
include "cardsdomel.mm"
include "mp2an.mm"
include "eleq2i.mm"
include "bitri.mm"
include "sylib.mm"
include "ensdomtr.mm"
include "mpancom.mm"
include "adantl.mm"
include "alephcard.mm"
include "jca.mm"
include "mto.mm"

theorem alephnbtwn2
  let cA: class A
  let cB: class B


  assert |- -. ( ( aleph ` A ) ~< B /\ B ~< ( aleph ` suc A ) )

  proof
    cA
    cale
    cfv
    #
    cB
    csdm
    wbr
    #
    cB
    cA
    csuc
    #
    cale
    cfv
    #
    csdm
    wbr
    #
    wa
    #
    @0
    cB
    ccrd
    cfv
    #
    wcel
    #
    @6
    @3
    wcel
    #
    wa
    #
    @6
    ccrd
    cfv
    #
    @6
    wceq
    @9
    wn
    cB
    cardidm
    #
    cA
    @6
    alephnbtwn
    ax-mp
    @5
    @7
    @8
    @5
    @0
    @6
    csdm
    wbr
    #
    @7
    @4
    @1
    cB
    @6
    cen
    wbr
    @12
    @4
    @6
    cB
    @4
    cB
    ccrd
    cdm
    #
    wcel
    #
    @6
    cB
    cen
    wbr
    #
    @4
    @3
    con0
    wcel
    #
    cB
    @3
    cdom
    wbr
    @14
    @2
    alephon
    #
    cB
    @3
    sdomdom
    @3
    cB
    ondomen
    sylancr
    cB
    cardid2
    syl
    #
    ensymd
    @0
    cB
    @6
    sdomentr
    sylan2
    @12
    @0
    @10
    wcel
    #
    @7
    @0
    con0
    wcel
    @6
    @13
    wcel
    #
    @12
    @19
    wb
    cA
    alephon
    @6
    con0
    wcel
    #
    @20
    cB
    cardon
    #
    @6
    onenon
    ax-mp
    @0
    @6
    cardsdomel
    mp2an
    @10
    @6
    @0
    @11
    eleq2i
    bitri
    sylib
    @5
    @6
    @3
    csdm
    wbr
    #
    @8
    @4
    @23
    @1
    @15
    @4
    @23
    @18
    @6
    cB
    @3
    ensdomtr
    mpancom
    adantl
    @23
    @6
    @3
    ccrd
    cfv
    #
    wcel
    #
    @8
    @21
    @3
    @13
    wcel
    #
    @23
    @25
    wb
    @22
    @16
    @26
    @17
    @3
    onenon
    ax-mp
    @6
    @3
    cardsdomel
    mp2an
    @24
    @3
    @6
    @2
    alephcard
    eleq2i
    bitri
    sylib
    jca
    mto
end
