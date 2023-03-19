include "wceq.mm"
include "wn.mm"
include "id.mm"
include "neqned.mm"

theorem neqne
  let cA: class A
  let cB: class B


  assert |- ( -. A = B -> A =/= B )

  proof
    cA
    cB
    wceq
    wn
    #
    cA
    cB
    @0
    id
    neqned
end
