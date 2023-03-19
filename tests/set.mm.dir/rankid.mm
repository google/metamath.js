include "cr1.mm"
include "con0.mm"
include "cima.mm"
include "cuni.mm"
include "wcel.mm"
include "crnk.mm"
include "cfv.mm"
include "csuc.mm"
include "cvv.mm"
include "unir1.mm"
include "eleqtrri.mm"
include "rankidb.mm"
include "ax-mp.mm"

theorem rankid
  let cA: class A
  assume rankid.1: |- A e. _V


  assert |- A e. ( R1 ` suc ( rank ` A ) )

  proof
    cA
    cr1
    con0
    cima
    cuni
    #
    wcel
    cA
    cA
    crnk
    cfv
    csuc
    cr1
    cfv
    wcel
    cA
    cvv
    @0
    rankid.1
    unir1
    eleqtrri
    cA
    rankidb
    ax-mp
end
