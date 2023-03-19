include "cr1.mm"
include "con0.mm"
include "cima.mm"
include "cuni.mm"
include "wcel.mm"
include "csn.mm"
include "crnk.mm"
include "cfv.mm"
include "csuc.mm"
include "wceq.mm"
include "cvv.mm"
include "unir1.mm"
include "eleqtrri.mm"
include "ranksnb.mm"
include "ax-mp.mm"

theorem ranksn
  let cA: class A
  let vx: setvar x
  assume ranksn.1: |- A e. _V


  assert |- ( rank ` { A } ) = suc ( rank ` A )

  proof
    cA
    cr1
    con0
    cima
    cuni
    #
    wcel
    cA
    csn
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
    ranksn.1
    unir1
    eleqtrri
    cA
    ranksnb
    ax-mp
end
