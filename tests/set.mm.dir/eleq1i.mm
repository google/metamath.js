include "wceq.mm"
include "wcel.mm"
include "wb.mm"
include "eleq1.mm"
include "ax-mp.mm"

theorem eleq1i
  let cA: class A
  let cB: class B
  let cC: class C
  assume eleq1i.1: |- A = B


  assert |- ( A e. C <-> B e. C )

  proof
    cA
    cB
    wceq
    cA
    cC
    wcel
    cB
    cC
    wcel
    wb
    eleq1i.1
    cA
    cB
    cC
    eleq1
    ax-mp
end
