include "wrel.mm"
include "cvv.mm"
include "cxp.mm"
include "wss.mm"
include "df-rel.mm"
include "nfcv.mm"
include "nfss.mm"
include "nfxfr.mm"

theorem nfrel
  let vx: setvar x
  let cA: class A
  assume nfrel.1: |- F/_ x A


  assert |- F/ x Rel A

  proof
    cA
    wrel
    cA
    cvv
    cvv
    cxp
    #
    wss
    vx
    cA
    df-rel
    vx
    cA
    @0
    nfrel.1
    vx
    @0
    nfcv
    nfss
    nfxfr
end
