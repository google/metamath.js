include "wceq.mm"
include "wb.mm"
include "eqeq1.mm"
include "ax-mp.mm"

theorem eqeq1i
  let cA: class A
  let cB: class B
  let cC: class C
  assume eqeq1i.1: |- A = B


  assert |- ( A = C <-> B = C )

  proof
    cA
    cB
    wceq
    cA
    cC
    wceq
    cB
    cC
    wceq
    wb
    eqeq1i.1
    cA
    cB
    cC
    eqeq1
    ax-mp
end
