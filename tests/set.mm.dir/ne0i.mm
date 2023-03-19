include "wcel.mm"
include "c0.mm"
include "n0i.mm"
include "neqned.mm"

theorem ne0i
  let cA: class A
  let cB: class B


  assert |- ( B e. A -> A =/= (/) )

  proof
    cB
    cA
    wcel
    cA
    c0
    cA
    cB
    n0i
    neqned
end
