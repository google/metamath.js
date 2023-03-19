include "ctpos.mm"
include "cvv.mm"
include "cxp.mm"
include "c0.mm"
include "csn.mm"
include "cun.mm"
include "cv.mm"
include "ccnv.mm"
include "cuni.mm"
include "cmpt.mm"
include "ccom.mm"
include "dftpos4.mm"
include "nfcv.mm"
include "nfco.mm"
include "nfcxfr.mm"

theorem nftpos
  let vx: setvar x
  let cF: class F
  let vy: setvar y
  assume nftpos.1: |- F/_ x F


  assert |- F/_ x tpos F

  proof
    vx
    cF
    ctpos
    cF
    vy
    cvv
    cvv
    cxp
    c0
    csn
    cun
    vy
    cv
    csn
    ccnv
    cuni
    cmpt
    #
    ccom
    vy
    cF
    dftpos4
    vx
    cF
    @0
    nftpos.1
    vx
    @0
    nfcv
    nfco
    nfcxfr
end
