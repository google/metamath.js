include "cr.mm"
include "wcel.mm"
include "cabs.mm"
include "cfv.mm"
include "c2.mm"
include "cexp.mm"
include "co.mm"
include "csqrt.mm"
include "wceq.mm"
include "absre.mm"
include "ax-mp.mm"

theorem absrei
  let cA: class A
  assume sqrth.1: |- A e. RR


  assert |- ( abs ` A ) = ( sqrt ` ( A ^ 2 ) )

  proof
    cA
    cr
    wcel
    cA
    cabs
    cfv
    cA
    c2
    cexp
    co
    csqrt
    cfv
    wceq
    sqrth.1
    cA
    absre
    ax-mp
end
