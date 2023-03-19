include "wne.mm"
include "wceq.mm"
include "wa.mm"
include "wn.mm"
include "wo.mm"
include "eqtr3.mm"
include "necon3ai.mm"
include "neorian.mm"
include "sylibr.mm"

theorem neneor
  let cA: class A
  let cB: class B
  let cC: class C


  assert |- ( A =/= B -> ( A =/= C \/ B =/= C ) )

  proof
    cA
    cB
    wne
    cA
    cC
    wceq
    cB
    cC
    wceq
    wa
    #
    wn
    cA
    cC
    wne
    cB
    cC
    wne
    wo
    @0
    cA
    cB
    cA
    cB
    cC
    eqtr3
    necon3ai
    cA
    cC
    cB
    cC
    neorian
    sylibr
end
