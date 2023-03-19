include "csn.mm"
include "wcel.mm"
include "elsni.mm"
include "necon3ai.mm"

theorem nelsn
  let cA: class A
  let cB: class B


  assert |- ( A =/= B -> -. A e. { B } )

  proof
    cA
    cB
    csn
    wcel
    cA
    cB
    cA
    cB
    elsni
    necon3ai
end
