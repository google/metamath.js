include "wceq.mm"
include "id.mm"
include "eleq1d.mm"

theorem eleq1
  param cA: class A
  param cB: class B
  param cC: class C


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
