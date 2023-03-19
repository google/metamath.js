include "cr1.mm"
include "con0.mm"
include "cima.mm"
include "cuni.mm"
include "wcel.mm"
include "c0.mm"
include "wceq.mm"
include "crnk.mm"
include "cfv.mm"
include "wb.mm"
include "cvv.mm"
include "unir1.mm"
include "eleqtrri.mm"
include "rankeq0b.mm"
include "ax-mp.mm"

theorem rankeq0
  let cA: class A
  assume rankeq0.1: |- A e. _V


  assert |- ( A = (/) <-> ( rank ` A ) = (/) )

  proof
    cA
    cr1
    con0
    cima
    cuni
    #
    wcel
    cA
    c0
    wceq
    cA
    crnk
    cfv
    c0
    wceq
    wb
    cA
    cvv
    @0
    rankeq0.1
    unir1
    eleqtrri
    cA
    rankeq0b
    ax-mp
end
