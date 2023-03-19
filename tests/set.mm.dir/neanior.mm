include "wne.mm"
include "wa.mm"
include "wceq.mm"
include "wn.mm"
include "wo.mm"
include "df-ne.mm"
include "anbi12i.mm"
include "pm4.56.mm"
include "bitri.mm"

theorem neanior
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D


  assert |- ( ( A =/= B /\ C =/= D ) <-> -. ( A = B \/ C = D ) )

  proof
    cA
    cB
    wne
    #
    cC
    cD
    wne
    #
    wa
    cA
    cB
    wceq
    #
    wn
    #
    cC
    cD
    wceq
    #
    wn
    #
    wa
    @2
    @4
    wo
    wn
    @0
    @3
    @1
    @5
    cA
    cB
    df-ne
    cC
    cD
    df-ne
    anbi12i
    @2
    @4
    pm4.56
    bitri
end
