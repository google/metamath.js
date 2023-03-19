include "cres.mm"
include "cvv.mm"
include "cxp.mm"
include "cin.mm"
include "df-res.mm"
include "nfcv.mm"
include "nfxp.mm"
include "nfin.mm"
include "nfcxfr.mm"

theorem nfres
  let vx: setvar x
  let cA: class A
  let cB: class B
  assume nfres.1: |- F/_ x A
  assume nfres.2: |- F/_ x B


  assert |- F/_ x ( A |` B )

  proof
    vx
    cA
    cB
    cres
    cA
    cB
    cvv
    cxp
    #
    cin
    cA
    cB
    df-res
    vx
    cA
    @0
    nfres.1
    vx
    cB
    cvv
    nfres.2
    vx
    cvv
    nfcv
    nfxp
    nfin
    nfcxfr
end
