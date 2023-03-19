include "wceq.mm"
include "csn.mm"
include "sneq.mm"
include "ax-mp.mm"

theorem sneqi
  let cA: class A
  let cB: class B
  assume sneqi.1: |- A = B


  assert |- { A } = { B }

  proof
    cA
    cB
    wceq
    cA
    csn
    cB
    csn
    wceq
    sneqi.1
    cA
    cB
    sneq
    ax-mp
end
