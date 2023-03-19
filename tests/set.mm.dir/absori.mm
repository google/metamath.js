include "cr.mm"
include "wcel.mm"
include "cabs.mm"
include "cfv.mm"
include "wceq.mm"
include "cneg.mm"
include "wo.mm"
include "absor.mm"
include "ax-mp.mm"

theorem absori
  let cA: class A
  assume sqrth.1: |- A e. RR


  assert |- ( ( abs ` A ) = A \/ ( abs ` A ) = -u A )

  proof
    cA
    cr
    wcel
    cA
    cabs
    cfv
    #
    cA
    wceq
    @0
    cA
    cneg
    wceq
    wo
    sqrth.1
    cA
    absor
    ax-mp
end
