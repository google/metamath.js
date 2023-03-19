include "wss.mm"
include "wa.mm"
include "cdif.mm"
include "wceq.mm"
include "ancom.mm"
include "wb.mm"
include "sscon34b.mm"
include "ancoms.mm"
include "anbi12d.mm"
include "syl5bb.mm"
include "eqss.mm"
include "3bitr4g.mm"

theorem rcompleq
  let cA: class A
  let cB: class B
  let cC: class C


  assert |- ( ( A C_ C /\ B C_ C ) -> ( A = B <-> ( C \ A ) = ( C \ B ) ) )

  proof
    cA
    cC
    wss
    #
    cB
    cC
    wss
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
    wa
    #
    cC
    cA
    cdif
    #
    cC
    cB
    cdif
    #
    wss
    #
    @7
    @6
    wss
    #
    wa
    #
    cA
    cB
    wceq
    @6
    @7
    wceq
    @5
    @4
    @3
    wa
    @2
    @10
    @3
    @4
    ancom
    @2
    @4
    @8
    @3
    @9
    @1
    @0
    @4
    @8
    wb
    cB
    cA
    cC
    sscon34b
    ancoms
    cA
    cB
    cC
    sscon34b
    anbi12d
    syl5bb
    cA
    cB
    eqss
    @6
    @7
    eqss
    3bitr4g
end
