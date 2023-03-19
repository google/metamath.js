include "wceq.mm"
include "id.mm"
include "eqidd.mm"
include "neleq12d.mm"

theorem neleq1
  let cA: class A
  let cB: class B
  let cC: class C


  assert |- ( A = B -> ( A e/ C <-> B e/ C ) )

  proof
    cA
    cB
    wceq
    #
    cA
    cB
    cC
    cC
    @0
    id
    @0
    cC
    eqidd
    neleq12d
end
