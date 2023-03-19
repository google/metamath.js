include "wceq.mm"
include "wne.mm"
include "eqeq1.mm"
include "biimprd.mm"
include "necon3d.mm"
include "imp.mm"

theorem pm13.18
  let cA: class A
  let cB: class B
  let cC: class C


  assert |- ( ( A = B /\ A =/= C ) -> B =/= C )

  proof
    cA
    cB
    wceq
    #
    cA
    cC
    wne
    cB
    cC
    wne
    @0
    cB
    cC
    cA
    cC
    @0
    cA
    cC
    wceq
    cB
    cC
    wceq
    cA
    cB
    cC
    eqeq1
    biimprd
    necon3d
    imp
end
