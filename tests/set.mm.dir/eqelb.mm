include "wceq.mm"
include "wcel.mm"
include "wa.mm"
include "simpl.mm"
include "eqeltr.mm"
include "jca.mm"
include "eqcom.mm"
include "anbi1i.mm"
include "3imtr3i.mm"
include "impbii.mm"

theorem eqelb
  let cA: class A
  let cB: class B
  let cC: class C


  assert |- ( ( A = B /\ A e. C ) <-> ( A = B /\ B e. C ) )

  proof
    cA
    cB
    wceq
    #
    cA
    cC
    wcel
    #
    wa
    #
    @0
    cB
    cC
    wcel
    #
    wa
    #
    cB
    cA
    wceq
    #
    @1
    wa
    #
    @5
    @3
    wa
    @2
    @4
    @6
    @5
    @3
    @5
    @1
    simpl
    cB
    cA
    cC
    eqeltr
    jca
    @5
    @0
    @1
    cB
    cA
    eqcom
    #
    anbi1i
    @5
    @0
    @3
    @7
    anbi1i
    3imtr3i
    @4
    @0
    @1
    @0
    @3
    simpl
    cA
    cB
    cC
    eqeltr
    jca
    impbii
end
