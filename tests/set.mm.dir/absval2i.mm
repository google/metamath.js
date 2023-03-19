include "cc.mm"
include "wcel.mm"
include "cabs.mm"
include "cfv.mm"
include "cre.mm"
include "c2.mm"
include "cexp.mm"
include "co.mm"
include "cim.mm"
include "caddc.mm"
include "csqrt.mm"
include "wceq.mm"
include "absval2.mm"
include "ax-mp.mm"

theorem absval2i
  let cA: class A
  assume absvalsqi.1: |- A e. CC


  assert |- ( abs ` A ) = ( sqrt ` ( ( ( Re ` A ) ^ 2 ) + ( ( Im ` A ) ^ 2 ) ) )

  proof
    cA
    cc
    wcel
    cA
    cabs
    cfv
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
    csqrt
    cfv
    wceq
    absvalsqi.1
    cA
    absval2
    ax-mp
end
