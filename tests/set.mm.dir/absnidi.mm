include "cr.mm"
include "wcel.mm"
include "cc0.mm"
include "cle.mm"
include "wbr.mm"
include "cabs.mm"
include "cfv.mm"
include "cneg.mm"
include "wceq.mm"
include "absnid.mm"
include "mpan.mm"

theorem absnidi
  let cA: class A
  assume sqrth.1: |- A e. RR


  assert |- ( A <_ 0 -> ( abs ` A ) = -u A )

  proof
    cA
    cr
    wcel
    cA
    cc0
    cle
    wbr
    cA
    cabs
    cfv
    cA
    cneg
    wceq
    sqrth.1
    cA
    absnid
    mpan
end
