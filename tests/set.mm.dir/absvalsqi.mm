include "cc.mm"
include "wcel.mm"
include "cabs.mm"
include "cfv.mm"
include "c2.mm"
include "cexp.mm"
include "co.mm"
include "ccj.mm"
include "cmul.mm"
include "wceq.mm"
include "absvalsq.mm"
include "ax-mp.mm"

theorem absvalsqi
  let cA: class A
  assume absvalsqi.1: |- A e. CC


  assert |- ( ( abs ` A ) ^ 2 ) = ( A x. ( * ` A ) )

  proof
    cA
    cc
    wcel
    cA
    cabs
    cfv
    c2
    cexp
    co
    cA
    cA
    ccj
    cfv
    cmul
    co
    wceq
    absvalsqi.1
    cA
    absvalsq
    ax-mp
end
