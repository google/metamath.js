include "wceq.mm"
include "id.mm"
include "eleq2d.mm"

theorem eleq2
  let cA: class A
  let cB: class B
  let cC: class C


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
