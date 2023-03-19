include "cc.mm"
include "wcel.mm"
include "cre.mm"
include "cfv.mm"
include "cabs.mm"
include "cle.mm"
include "wbr.mm"
include "releabs.mm"
include "ax-mp.mm"

theorem releabsi
  let cA: class A
  assume absvalsqi.1: |- A e. CC


  assert |- ( Re ` A ) <_ ( abs ` A )

  proof
    cA
    cc
    wcel
    cA
    cre
    cfv
    cA
    cabs
    cfv
    cle
    wbr
    absvalsqi.1
    cA
    releabs
    ax-mp
end
