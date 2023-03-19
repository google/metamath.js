include "con0.mm"
include "wcel.mm"
include "ccrd.mm"
include "cdm.mm"
include "wa.mm"
include "csdm.mm"
include "wbr.mm"
include "cfv.mm"
include "wi.mm"
include "cen.mm"
include "cardid2.mm"
include "ensymd.mm"
include "sdomentr.mm"
include "sylan2.mm"
include "wss.mm"
include "wn.mm"
include "cdom.mm"
include "ssdomg.mm"
include "wb.mm"
include "cardon.mm"
include "domtriord.mm"
include "mpan.mm"
include "sylibd.mm"
include "con2d.mm"
include "ontri1.mm"
include "con2bid.mm"
include "sylibrd.mm"
include "syl5.mm"
include "expcomd.mm"
include "imp.mm"
include "cardsdomelir.mm"
include "impbid1.mm"

theorem cardsdomel
  let cA: class A
  let cB: class B


  assert |- ( ( A e. On /\ B e. dom card ) -> ( A ~< B <-> A e. ( card ` B ) ) )

  proof
    cA
    con0
    wcel
    #
    cB
    ccrd
    cdm
    wcel
    #
    wa
    cA
    cB
    csdm
    wbr
    #
    cA
    cB
    ccrd
    cfv
    #
    wcel
    #
    @0
    @1
    @2
    @4
    wi
    @0
    @2
    @1
    @4
    @2
    @1
    wa
    cA
    @3
    csdm
    wbr
    #
    @0
    @4
    @1
    @2
    cB
    @3
    cen
    wbr
    @5
    @1
    @3
    cB
    cB
    cardid2
    ensymd
    cA
    cB
    @3
    sdomentr
    sylan2
    @0
    @5
    @3
    cA
    wss
    #
    wn
    @4
    @0
    @6
    @5
    @0
    @6
    @3
    cA
    cdom
    wbr
    #
    @5
    wn
    #
    @3
    cA
    con0
    ssdomg
    @3
    con0
    wcel
    #
    @0
    @7
    @8
    wb
    cB
    cardon
    #
    @3
    cA
    domtriord
    mpan
    sylibd
    con2d
    @0
    @6
    @4
    @9
    @0
    @6
    @4
    wn
    wb
    @10
    @3
    cA
    ontri1
    mpan
    con2bid
    sylibrd
    syl5
    expcomd
    imp
    cA
    cB
    cardsdomelir
    impbid1
end
