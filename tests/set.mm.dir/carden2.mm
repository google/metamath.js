include "ccrd.mm"
include "cdm.mm"
include "wcel.mm"
include "wa.mm"
include "cfv.mm"
include "wss.mm"
include "cdom.mm"
include "wbr.mm"
include "wceq.mm"
include "cen.mm"
include "carddom2.mm"
include "wb.mm"
include "ancoms.mm"
include "anbi12d.mm"
include "eqss.mm"
include "bicomi.mm"
include "sbthb.mm"
include "3bitr3g.mm"

theorem carden2
  let cA: class A
  let cB: class B


  assert |- ( ( A e. dom card /\ B e. dom card ) -> ( ( card ` A ) = ( card ` B ) <-> A ~~ B ) )

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
    @5
    @4
    wss
    #
    wa
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
    wa
    @4
    @5
    wceq
    #
    cA
    cB
    cen
    wbr
    @3
    @6
    @9
    @7
    @10
    cA
    cB
    carddom2
    @2
    @1
    @7
    @10
    wb
    cB
    cA
    carddom2
    ancoms
    anbi12d
    @11
    @8
    @4
    @5
    eqss
    bicomi
    cA
    cB
    sbthb
    3bitr3g
end
