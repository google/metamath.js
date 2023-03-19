include "cch.mm"
include "wcel.mm"
include "wa.mm"
include "wss.mm"
include "wn.mm"
include "cort.mm"
include "cfv.mm"
include "wpss.mm"
include "chsscon3.mm"
include "wb.mm"
include "ancoms.mm"
include "notbid.mm"
include "anbi12d.mm"
include "dfpss3.mm"
include "3bitr4g.mm"

theorem chpsscon3
  let cA: class A
  let cB: class B


  assert |- ( ( A e. CH /\ B e. CH ) -> ( A C. B <-> ( _|_ ` B ) C. ( _|_ ` A ) ) )

  proof
    cA
    cch
    wcel
    #
    cB
    cch
    wcel
    #
    wa
    #
    cA
    cB
    wss
    #
    cB
    cA
    wss
    #
    wn
    #
    wa
    cB
    cort
    cfv
    #
    cA
    cort
    cfv
    #
    wss
    #
    @7
    @6
    wss
    #
    wn
    #
    wa
    cA
    cB
    wpss
    @6
    @7
    wpss
    @2
    @3
    @8
    @5
    @10
    cA
    cB
    chsscon3
    @2
    @4
    @9
    @1
    @0
    @4
    @9
    wb
    cB
    cA
    chsscon3
    ancoms
    notbid
    anbi12d
    cA
    cB
    dfpss3
    @6
    @7
    dfpss3
    3bitr4g
end
