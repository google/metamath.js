include "wceq.mm"
include "id.mm"
include "eleq2d.mm"

theorem eleq2
  param cA: class A
  param cB: class B
  param cC: class C


  assert |- ( A = B -> ( C e. A <-> C e. B ) )

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
    eleq2d
end
