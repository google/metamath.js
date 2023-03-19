include "cr.mm"
include "wcel.mm"
include "cc0.mm"
include "cle.mm"
include "wbr.mm"
include "cabs.mm"
include "cfv.mm"
include "wceq.mm"
include "absid.mm"
include "mpan.mm"

theorem absidi
  let cA: class A
  assume sqrth.1: |- A e. RR


  assert |- ( 0 <_ A -> ( abs ` A ) = A )

  proof
    cA
    cr
    wcel
    cc0
    cA
    cle
    wbr
    cA
    cabs
    cfv
    cA
    wceq
    sqrth.1
    cA
    absid
    mpan
end
