include "cr.mm"
include "wcel.mm"
include "cneg.mm"
include "cfl.mm"
include "cfv.mm"
include "cceil.mm"
include "cle.mm"
include "ceige.mm"
include "ceilval.mm"
include "breqtrrd.mm"

theorem ceilge
  let cA: class A


  assert |- ( A e. RR -> A <_ ( |^ ` A ) )

  proof
    cA
    cr
    wcel
    cA
    cA
    cneg
    cfl
    cfv
    cneg
    cA
    cceil
    cfv
    cle
    cA
    ceige
    cA
    ceilval
    breqtrrd
end
