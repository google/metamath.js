include "wceq.mm"
include "id.mm"
include "eqeq2d.mm"

theorem eqeq2
  param cA: class A
  param cB: class B
  param cC: class C


  assert |- ( A = B -> ( C = A <-> C = B ) )

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
    eqeq2d
end
