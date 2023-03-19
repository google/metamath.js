include "wceq.mm"
include "cop.mm"
include "opeq1.mm"
include "ax-mp.mm"

theorem opeq1i
  let cA: class A
  let cB: class B
  let cC: class C
  assume opeq1i.1: |- A = B


  assert |- <. A , C >. = <. B , C >.

  proof
    cA
    cB
    wceq
    cA
    cC
    cop
    cB
    cC
    cop
    wceq
    opeq1i.1
    cA
    cB
    cC
    opeq1
    ax-mp
end
