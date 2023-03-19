include "wceq.mm"
include "cop.mm"
include "opeq2.mm"
include "ax-mp.mm"

theorem opeq2i
  let cA: class A
  let cB: class B
  let cC: class C
  assume opeq1i.1: |- A = B


  assert |- <. C , A >. = <. C , B >.

  proof
    cA
    cB
    wceq
    cC
    cA
    cop
    cC
    cB
    cop
    wceq
    opeq1i.1
    cA
    cB
    cC
    opeq2
    ax-mp
end
