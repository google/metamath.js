include "wss.mm"
include "csn.mm"
include "cun.mm"
include "wa.mm"
include "wo.mm"
include "wceq.mm"
include "ssunsn2.mm"
include "ancom.mm"
include "eqss.mm"
include "bitr4i.mm"
include "orbi12i.mm"
include "bitri.mm"

theorem ssunsn
  let cA: class A
  let cB: class B
  let cC: class C
  let vx: setvar x


  assert |- ( ( B C_ A /\ A C_ ( B u. { C } ) ) <-> ( A = B \/ A = ( B u. { C } ) ) )

  proof
    cB
    cA
    wss
    #
    cA
    cB
    cC
    csn
    cun
    #
    wss
    #
    wa
    @0
    cA
    cB
    wss
    #
    wa
    #
    @1
    cA
    wss
    #
    @2
    wa
    #
    wo
    cA
    cB
    wceq
    #
    cA
    @1
    wceq
    #
    wo
    cA
    cB
    cB
    cC
    ssunsn2
    @4
    @7
    @6
    @8
    @4
    @3
    @0
    wa
    @7
    @0
    @3
    ancom
    cA
    cB
    eqss
    bitr4i
    @6
    @2
    @5
    wa
    @8
    @5
    @2
    ancom
    cA
    @1
    eqss
    bitr4i
    orbi12i
    bitri
end
