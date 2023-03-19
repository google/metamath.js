include "cc.mm"
include "wcel.mm"
include "cabs.mm"
include "cfv.mm"
include "c2.mm"
include "cexp.mm"
include "co.mm"
include "cre.mm"
include "cim.mm"
include "caddc.mm"
include "wceq.mm"
include "absvalsq2.mm"
include "ax-mp.mm"

theorem absvalsq2i
  let cA: class A
  assume absvalsqi.1: |- A e. CC


  assert |- ( ( abs ` A ) ^ 2 ) = ( ( ( Re ` A ) ^ 2 ) + ( ( Im ` A ) ^ 2 ) )

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
    cre
    cfv
    c2
    cexp
    co
    cA
    cim
    cfv
    c2
    cexp
    co
    caddc
    co
    wceq
    absvalsqi.1
    cA
    absvalsq2
    ax-mp
end
