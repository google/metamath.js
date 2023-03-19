include "cr1.mm"
include "con0.mm"
include "cima.mm"
include "cuni.mm"
include "wcel.mm"
include "cpw.mm"
include "crnk.mm"
include "cfv.mm"
include "csuc.mm"
include "wceq.mm"
include "cvv.mm"
include "unir1.mm"
include "eleqtrri.mm"
include "rankpwi.mm"
include "ax-mp.mm"

theorem rankpw
  let cA: class A
  assume rankpw.1: |- A e. _V


  assert |- ( rank ` ~P A ) = suc ( rank ` A )

  proof
    cA
    cr1
    con0
    cima
    cuni
    #
    wcel
    cA
    cpw
    crnk
    cfv
    cA
    crnk
    cfv
    csuc
    wceq
    cA
    cvv
    @0
    rankpw.1
    unir1
    eleqtrri
    cA
    rankpwi
    ax-mp
end
