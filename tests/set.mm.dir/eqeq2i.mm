include "wceq.mm"
include "wb.mm"
include "eqeq2.mm"
include "ax-mp.mm"

theorem eqeq2i
  param cA: class A
  param cB: class B
  param cC: class C
  assume eqeq2i.1: |- A = B


  assert |- ( C = A <-> C = B )

  proof
    cA
    cB
    wceq
    cC
    cA
    wceq
    cC
    cB
    wceq
    wb
    eqeq2i.1
    cA
    cB
    cC
    eqeq2
    ax-mp
end
