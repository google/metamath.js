include "cr1.mm"
include "con0.mm"
include "cima.mm"
include "cuni.mm"
include "wcel.mm"
include "cpr.mm"
include "crnk.mm"
include "cfv.mm"
include "cun.mm"
include "csuc.mm"
include "wceq.mm"
include "cvv.mm"
include "unir1.mm"
include "eleqtrri.mm"
include "rankprb.mm"
include "mp2an.mm"

theorem rankpr
  let cA: class A
  let cB: class B
  let vx: setvar x
  assume ranksn.1: |- A e. _V
  assume rankun.2: |- B e. _V


  assert |- ( rank ` { A , B } ) = suc ( ( rank ` A ) u. ( rank ` B ) )

  proof
    cA
    cr1
    con0
    cima
    cuni
    #
    wcel
    cB
    @0
    wcel
    cA
    cB
    cpr
    crnk
    cfv
    cA
    crnk
    cfv
    cB
    crnk
    cfv
    cun
    csuc
    wceq
    cA
    cvv
    @0
    ranksn.1
    unir1
    eleqtrri
    cB
    cvv
    @0
    rankun.2
    unir1
    eleqtrri
    cA
    cB
    rankprb
    mp2an
end
