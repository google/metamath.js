include "wceq.mm"
include "id.mm"
include "eleq1d.mm"

theorem eleq1
  let cA: class A
  let cB: class B
  let cC: class C


  assert |- ( A = B -> ( A e. C <-> B e. C ) )

  proof
    cA
    cB
    wceq
    #
    cA
    cB
    cC
    @0
    id
    eleq1d
end
