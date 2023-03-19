include "cr.mm"
include "wcel.mm"
include "cabs.mm"
include "cfv.mm"
include "cle.mm"
include "wbr.mm"
include "leabs.mm"
include "ax-mp.mm"

theorem leabsi
  let cA: class A
  assume sqrth.1: |- A e. RR


  assert |- A <_ ( abs ` A )

  proof
    cA
    cr
    wcel
    cA
    cA
    cabs
    cfv
    cle
    wbr
    sqrth.1
    cA
    leabs
    ax-mp
end
