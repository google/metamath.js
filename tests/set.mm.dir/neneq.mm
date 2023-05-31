include "wne.mm"
include "id.mm"
include "neneqd.mm"

theorem neneq
  param cA: class A
  param cB: class B


  assert |- ( A =/= B -> -. A = B )

  proof
    cA
    cB
    wne
    #
    cA
    cB
    @0
    id
    neneqd
end
