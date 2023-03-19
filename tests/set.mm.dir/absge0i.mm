include "cc.mm"
include "wcel.mm"
include "cc0.mm"
include "cabs.mm"
include "cfv.mm"
include "cle.mm"
include "wbr.mm"
include "absge0.mm"
include "ax-mp.mm"

theorem absge0i
  let cA: class A
  assume absvalsqi.1: |- A e. CC


  assert |- 0 <_ ( abs ` A )

  proof
    cA
    cc
    wcel
    cc0
    cA
    cabs
    cfv
    cle
    wbr
    absvalsqi.1
    cA
    absge0
    ax-mp
end
