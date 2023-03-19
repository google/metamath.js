include "wne.mm"
include "wa.mm"
include "cpr.mm"
include "csn.mm"
include "cin.mm"
include "c0.mm"
include "dfsn2.mm"
include "ineq2i.mm"
include "wceq.mm"
include "disjpr2.mm"
include "anidms.mm"
include "syl5eq.mm"

theorem disjprsn
  let cA: class A
  let cB: class B
  let cC: class C


  assert |- ( ( A =/= C /\ B =/= C ) -> ( { A , B } i^i { C } ) = (/) )

  proof
    cA
    cC
    wne
    cB
    cC
    wne
    wa
    #
    cA
    cB
    cpr
    #
    cC
    csn
    #
    cin
    @1
    cC
    cC
    cpr
    #
    cin
    #
    c0
    @2
    @3
    @1
    cC
    dfsn2
    ineq2i
    @0
    @4
    c0
    wceq
    cA
    cB
    cC
    cC
    disjpr2
    anidms
    syl5eq
end
