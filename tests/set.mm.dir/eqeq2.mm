include "wceq.mm"
include "id.mm"
include "eqeq2d.mm"

theorem eqeq2
  let cA: class A
  let cB: class B
  let cC: class C


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
