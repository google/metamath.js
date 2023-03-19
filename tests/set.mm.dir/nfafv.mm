include "cafv.mm"
include "wdfat.mm"
include "cfv.mm"
include "cvv.mm"
include "cif.mm"
include "dfafv2.mm"
include "nfdfat.mm"
include "nffv.mm"
include "nfcv.mm"
include "nfif.mm"
include "nfcxfr.mm"

theorem nfafv
  let vx: setvar x
  let cA: class A
  let cF: class F
  let vk: setvar k
  assume nfafv.1: |- F/_ x F
  assume nfafv.2: |- F/_ x A


  assert |- F/_ x ( F ''' A )

  proof
    vx
    cA
    cF
    cafv
    cA
    cF
    wdfat
    #
    cA
    cF
    cfv
    #
    cvv
    cif
    cA
    cF
    dfafv2
    @0
    vx
    @1
    cvv
    vx
    cA
    cF
    nfafv.1
    nfafv.2
    nfdfat
    vx
    cA
    cF
    nfafv.1
    nfafv.2
    nffv
    vx
    cvv
    nfcv
    nfif
    nfcxfr
end
