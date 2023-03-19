include "wne.mm"
include "wo.mm"
include "wceq.mm"
include "wn.mm"
include "wa.mm"
include "df-ne.mm"
include "orbi12i.mm"
include "ianor.mm"
include "bitr4i.mm"

theorem neorian
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D


  assert |- ( ( A =/= B \/ C =/= D ) <-> -. ( A = B /\ C = D ) )

  proof
    cA
    cB
    wne
    #
    cC
    cD
    wne
    #
    wo
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
    wo
    @2
    @4
    wa
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
    orbi12i
    @2
    @4
    ianor
    bitr4i
end
