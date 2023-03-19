include "cr1.mm"
include "con0.mm"
include "cima.mm"
include "cuni.mm"
include "wcel.mm"
include "wss.mm"
include "crnk.mm"
include "cfv.mm"
include "wi.mm"
include "cvv.mm"
include "unir1.mm"
include "eleqtrri.mm"
include "rankssb.mm"
include "ax-mp.mm"

theorem rankss
  let cA: class A
  let cB: class B
  assume rankss.1: |- B e. _V


  assert |- ( A C_ B -> ( rank ` A ) C_ ( rank ` B ) )

  proof
    cB
    cr1
    con0
    cima
    cuni
    #
    wcel
    cA
    cB
    wss
    cA
    crnk
    cfv
    cB
    crnk
    cfv
    wss
    wi
    cB
    cvv
    @0
    rankss.1
    unir1
    eleqtrri
    cA
    cB
    rankssb
    ax-mp
end
