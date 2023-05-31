include "wceq.mm"
include "id.mm"
include "eqeq1d.mm"

theorem eqeq1
  param cA: class A
  param cB: class B
  param cC: class C


  assert |- ( A = B -> ( A = C <-> B = C ) )

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
    eqeq1d
end
