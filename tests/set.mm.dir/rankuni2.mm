include "cr1.mm"
include "con0.mm"
include "cima.mm"
include "cuni.mm"
include "wcel.mm"
include "crnk.mm"
include "cfv.mm"
include "cv.mm"
include "ciun.mm"
include "wceq.mm"
include "cvv.mm"
include "unir1.mm"
include "eleqtrri.mm"
include "rankuni2b.mm"
include "ax-mp.mm"

theorem rankuni2
  let vx: setvar x
  let cA: class A
  assume ranksn.1: |- A e. _V

  disjoint A x
  assert |- ( rank ` U. A ) = U_ x e. A ( rank ` x )

  proof
    cA
    cr1
    con0
    cima
    cuni
    #
    wcel
    cA
    cuni
    crnk
    cfv
    vx
    cA
    vx
    cv
    crnk
    cfv
    ciun
    wceq
    cA
    cvv
    @0
    ranksn.1
    unir1
    eleqtrri
    vx
    cA
    rankuni2b
    ax-mp
end
