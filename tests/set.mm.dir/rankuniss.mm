include "cuni.mm"
include "crnk.mm"
include "cfv.mm"
include "rankuni.mm"
include "word.mm"
include "wss.mm"
include "rankon.mm"
include "onordi.mm"
include "orduniss.mm"
include "ax-mp.mm"
include "eqsstri.mm"

theorem rankuniss
  let cA: class A
  let vx: setvar x
  let vy: setvar y
  let cB: class B
  assume rankr1b.1: |- A e. _V


  assert |- ( rank ` U. A ) C_ ( rank ` A )

  proof
    cA
    cuni
    crnk
    cfv
    cA
    crnk
    cfv
    #
    cuni
    #
    @0
    cA
    rankuni
    @0
    word
    @1
    @0
    wss
    @0
    cA
    rankon
    onordi
    @0
    orduniss
    ax-mp
    eqsstri
end
