include "cc.mm"
include "wcel.mm"
include "cabs.mm"
include "cfv.mm"
include "cr.mm"
include "abscl.mm"
include "ax-mp.mm"

theorem abscli
  let cA: class A
  assume absvalsqi.1: |- A e. CC


  assert |- ( abs ` A ) e. RR

  proof
    cA
    cc
    wcel
    cA
    cabs
    cfv
    cr
    wcel
    absvalsqi.1
    cA
    abscl
    ax-mp
end
