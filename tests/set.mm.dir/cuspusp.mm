include "ccusp.mm"
include "wcel.mm"
include "cusp.mm"
include "cv.mm"
include "cuss.mm"
include "cfv.mm"
include "ccfilu.mm"
include "ctopn.mm"
include "cflim.mm"
include "co.mm"
include "c0.mm"
include "wne.mm"
include "wi.mm"
include "cbs.mm"
include "cfil.mm"
include "wral.mm"
include "iscusp.mm"
include "simplbi.mm"

theorem cuspusp
  let cW: class W
  let vc: setvar c
  let vw: setvar w


  assert |- ( W e. CUnifSp -> W e. UnifSp )

  proof
    cW
    ccusp
    wcel
    cW
    cusp
    wcel
    vc
    cv
    #
    cW
    cuss
    cfv
    ccfilu
    cfv
    wcel
    cW
    ctopn
    cfv
    @0
    cflim
    co
    c0
    wne
    wi
    vc
    cW
    cbs
    cfv
    cfil
    cfv
    wral
    cW
    vc
    iscusp
    simplbi
end
