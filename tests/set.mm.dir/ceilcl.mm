include "cr.mm"
include "wcel.mm"
include "cceil.mm"
include "cfv.mm"
include "cneg.mm"
include "cfl.mm"
include "cz.mm"
include "ceilval.mm"
include "ceicl.mm"
include "eqeltrd.mm"

theorem ceilcl
  let cA: class A


  assert |- ( A e. RR -> ( |^ ` A ) e. ZZ )

  proof
    cA
    cr
    wcel
    cA
    cceil
    cfv
    cA
    cneg
    cfl
    cfv
    cneg
    cz
    cA
    ceilval
    cA
    ceicl
    eqeltrd
end
