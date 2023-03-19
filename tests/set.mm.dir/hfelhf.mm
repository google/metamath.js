include "wcel.mm"
include "chf.mm"
include "wa.mm"
include "crnk.mm"
include "cfv.mm"
include "rankelg.mm"
include "ancoms.mm"
include "com.mm"
include "wi.mm"
include "elhf2g.mm"
include "ibi.mm"
include "elnn.mm"
include "syl5ibr.mm"
include "expcomd.mm"
include "imp.mm"
include "sylan2.mm"
include "mpd.mm"

theorem hfelhf
  let cA: class A
  let cB: class B


  assert |- ( ( A e. B /\ B e. Hf ) -> A e. Hf )

  proof
    cA
    cB
    wcel
    #
    cB
    chf
    wcel
    #
    wa
    cA
    crnk
    cfv
    #
    cB
    crnk
    cfv
    #
    wcel
    #
    cA
    chf
    wcel
    #
    @1
    @0
    @4
    cA
    cB
    chf
    rankelg
    ancoms
    @1
    @0
    @3
    com
    wcel
    #
    @4
    @5
    wi
    #
    @1
    @6
    cB
    chf
    elhf2g
    ibi
    @0
    @6
    @7
    @0
    @4
    @6
    @5
    @4
    @6
    wa
    @5
    @0
    @2
    com
    wcel
    @2
    @3
    elnn
    cA
    cB
    elhf2g
    syl5ibr
    expcomd
    imp
    sylan2
    mpd
end
