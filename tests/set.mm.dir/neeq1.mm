include "wceq.mm"
include "id.mm"
include "neeq1d.mm"

theorem neeq1
  let cA: class A
  let cB: class B
  let cC: class C


  assert |- ( A = B -> ( A =/= C <-> B =/= C ) )

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
    neeq1d
end
