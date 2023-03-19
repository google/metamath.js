include "wceq.mm"
include "cuni.mm"
include "unieq.mm"
include "ax-mp.mm"

theorem unieqi
  let cA: class A
  let cB: class B
  assume unieqi.1: |- A = B


  assert |- U. A = U. B

  proof
    cA
    cB
    wceq
    cA
    cuni
    cB
    cuni
    wceq
    unieqi.1
    cA
    cB
    unieq
    ax-mp
end
