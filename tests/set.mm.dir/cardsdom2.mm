include "ccrd.mm"
include "cdm.mm"
include "wcel.mm"
include "wa.mm"
include "cfv.mm"
include "wss.mm"
include "wne.mm"
include "cdom.mm"
include "wbr.mm"
include "cen.mm"
include "wn.mm"
include "csdm.mm"
include "carddom2.mm"
include "carden2.mm"
include "necon3abid.mm"
include "anbi12d.mm"
include "con0.mm"
include "wb.mm"
include "cardon.mm"
include "onelpss.mm"
include "mp2an.mm"
include "brsdom.mm"
include "3bitr4g.mm"

theorem cardsdom2
  let cA: class A
  let cB: class B


  assert |- ( ( A e. dom card /\ B e. dom card ) -> ( ( card ` A ) e. ( card ` B ) <-> A ~< B ) )

  proof
    cA
    ccrd
    cdm
    #
    wcel
    cB
    @0
    wcel
    wa
    #
    cA
    ccrd
    cfv
    #
    cB
    ccrd
    cfv
    #
    wss
    #
    @2
    @3
    wne
    #
    wa
    #
    cA
    cB
    cdom
    wbr
    #
    cA
    cB
    cen
    wbr
    #
    wn
    #
    wa
    @2
    @3
    wcel
    #
    cA
    cB
    csdm
    wbr
    @1
    @4
    @7
    @5
    @9
    cA
    cB
    carddom2
    @1
    @8
    @2
    @3
    cA
    cB
    carden2
    necon3abid
    anbi12d
    @2
    con0
    wcel
    @3
    con0
    wcel
    @10
    @6
    wb
    cA
    cardon
    cB
    cardon
    @2
    @3
    onelpss
    mp2an
    cA
    cB
    brsdom
    3bitr4g
end
