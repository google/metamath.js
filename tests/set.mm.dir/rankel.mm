include "cr1.mm"
include "con0.mm"
include "cima.mm"
include "cuni.mm"
include "wcel.mm"
include "crnk.mm"
include "cfv.mm"
include "wi.mm"
include "cvv.mm"
include "unir1.mm"
include "eleqtrri.mm"
include "rankelb.mm"
include "ax-mp.mm"

theorem rankel
  let cA: class A
  let cB: class B
  assume rankel.1: |- B e. _V


  assert |- ( A e. B -> ( rank ` A ) e. ( rank ` B ) )

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
    wcel
    cA
    crnk
    cfv
    cB
    crnk
    cfv
    wcel
    wi
    cB
    cvv
    @0
    rankel.1
    unir1
    eleqtrri
    cA
    cB
    rankelb
    ax-mp
end
