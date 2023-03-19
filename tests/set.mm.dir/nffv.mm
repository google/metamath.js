include "cfv.mm"
include "cv.mm"
include "wbr.mm"
include "cio.mm"
include "df-fv.mm"
include "nfcv.mm"
include "nfbr.mm"
include "nfiota.mm"
include "nfcxfr.mm"

theorem nffv
  let vx: setvar x
  let cA: class A
  let cF: class F
  let vy: setvar y
  assume nffv.1: |- F/_ x F
  assume nffv.2: |- F/_ x A


  assert |- F/_ x ( F ` A )

  proof
    vx
    cA
    cF
    cfv
    cA
    vy
    cv
    #
    cF
    wbr
    #
    vy
    cio
    vy
    cA
    cF
    df-fv
    @1
    vx
    vy
    vx
    cA
    @0
    cF
    nffv.2
    nffv.1
    vx
    @0
    nfcv
    nfbr
    nfiota
    nfcxfr
end
