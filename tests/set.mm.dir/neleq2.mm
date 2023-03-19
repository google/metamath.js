include "wceq.mm"
include "eqidd.mm"
include "id.mm"
include "neleq12d.mm"

theorem neleq2
  let cA: class A
  let cB: class B
  let cC: class C


  assert |- ( A = B -> ( C e/ A <-> C e/ B ) )

  proof
    cA
    cB
    wceq
    #
    cC
    cC
    cA
    cB
    @0
    cC
    eqidd
    @0
    id
    neleq12d
end
