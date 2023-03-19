include "cc.mm"
include "wcel.mm"
include "cneg.mm"
include "cabs.mm"
include "cfv.mm"
include "wceq.mm"
include "absneg.mm"
include "ax-mp.mm"

theorem absnegi
  let cA: class A
  assume absvalsqi.1: |- A e. CC


  assert |- ( abs ` -u A ) = ( abs ` A )

  proof
    cA
    cc
    wcel
    cA
    cneg
    cabs
    cfv
    cA
    cabs
    cfv
    wceq
    absvalsqi.1
    cA
    absneg
    ax-mp
end
