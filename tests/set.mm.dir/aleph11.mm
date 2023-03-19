include "con0.mm"
include "wcel.mm"
include "wa.mm"
include "wceq.mm"
include "cale.mm"
include "cfv.mm"
include "wss.mm"
include "alephord3.mm"
include "wb.mm"
include "ancoms.mm"
include "anbi12d.mm"
include "eqss.mm"
include "3bitr4g.mm"
include "bicomd.mm"

theorem aleph11
  let cA: class A
  let cB: class B


  assert |- ( ( A e. On /\ B e. On ) -> ( ( aleph ` A ) = ( aleph ` B ) <-> A = B ) )

  proof
    cA
    con0
    wcel
    #
    cB
    con0
    wcel
    #
    wa
    #
    cA
    cB
    wceq
    #
    cA
    cale
    cfv
    #
    cB
    cale
    cfv
    #
    wceq
    #
    @2
    cA
    cB
    wss
    #
    cB
    cA
    wss
    #
    wa
    @4
    @5
    wss
    #
    @5
    @4
    wss
    #
    wa
    @3
    @6
    @2
    @7
    @9
    @8
    @10
    cA
    cB
    alephord3
    @1
    @0
    @8
    @10
    wb
    cB
    cA
    alephord3
    ancoms
    anbi12d
    cA
    cB
    eqss
    @4
    @5
    eqss
    3bitr4g
    bicomd
end
