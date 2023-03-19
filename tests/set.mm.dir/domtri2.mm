include "ccrd.mm"
include "cdm.mm"
include "wcel.mm"
include "wa.mm"
include "cfv.mm"
include "wss.mm"
include "cdom.mm"
include "wbr.mm"
include "csdm.mm"
include "wn.mm"
include "carddom2.mm"
include "con0.mm"
include "wb.mm"
include "cardon.mm"
include "ontri1.mm"
include "mp2an.mm"
include "cardsdom2.mm"
include "ancoms.mm"
include "notbid.mm"
include "syl5bb.mm"
include "bitr3d.mm"

theorem domtri2
  let cA: class A
  let cB: class B


  assert |- ( ( A e. dom card /\ B e. dom card ) -> ( A ~<_ B <-> -. B ~< A ) )

  proof
    cA
    ccrd
    cdm
    #
    wcel
    #
    cB
    @0
    wcel
    #
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
    cA
    cB
    cdom
    wbr
    cB
    cA
    csdm
    wbr
    #
    wn
    #
    cA
    cB
    carddom2
    @6
    @5
    @4
    wcel
    #
    wn
    #
    @3
    @8
    @4
    con0
    wcel
    @5
    con0
    wcel
    @6
    @10
    wb
    cA
    cardon
    cB
    cardon
    @4
    @5
    ontri1
    mp2an
    @3
    @9
    @7
    @2
    @1
    @9
    @7
    wb
    cB
    cA
    cardsdom2
    ancoms
    notbid
    syl5bb
    bitr3d
end
