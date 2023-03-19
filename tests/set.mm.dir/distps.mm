include "cpw.mm"
include "cuni.mm"
include "unipw.mm"
include "eqcomi.mm"
include "cvv.mm"
include "wcel.mm"
include "ctop.mm"
include "distop.mm"
include "ax-mp.mm"
include "eltpsi.mm"

theorem distps
  let cA: class A
  let cK: class K
  assume distps.a: |- A e. _V
  assume distps.k: |- K = { <. ( Base ` ndx ) , A >. , <. ( TopSet ` ndx ) , ~P A >. }


  assert |- K e. TopSp

  proof
    cA
    cA
    cpw
    #
    cK
    distps.k
    @0
    cuni
    cA
    cA
    unipw
    eqcomi
    cA
    cvv
    wcel
    @0
    ctop
    wcel
    distps.a
    cA
    cvv
    distop
    ax-mp
    eltpsi
end
