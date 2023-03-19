include "wceq.mm"
include "cxne.mm"
include "xnegeq.mm"
include "ax-mp.mm"

theorem xnegeqi
  let cA: class A
  let cB: class B
  assume xnegeqi.1: |- A = B


  assert |- -e A = -e B

  proof
    cA
    cB
    wceq
    cA
    cxne
    cB
    cxne
    wceq
    xnegeqi.1
    cA
    cB
    xnegeq
    ax-mp
end
