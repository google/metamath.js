include "cc.mm"
include "wcel.mm"
include "ccj.mm"
include "cfv.mm"
include "cabs.mm"
include "wceq.mm"
include "abscj.mm"
include "ax-mp.mm"

theorem abscji
  let cA: class A
  assume absvalsqi.1: |- A e. CC


  assert |- ( abs ` ( * ` A ) ) = ( abs ` A )

  proof
    cA
    cc
    wcel
    cA
    ccj
    cfv
    cabs
    cfv
    cA
    cabs
    cfv
    wceq
    absvalsqi.1
    cA
    abscj
    ax-mp
end
