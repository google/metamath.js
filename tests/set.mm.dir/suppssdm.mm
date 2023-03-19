include "cvv.mm"
include "wcel.mm"
include "wa.mm"
include "csupp.mm"
include "co.mm"
include "cdm.mm"
include "wss.mm"
include "cv.mm"
include "csn.mm"
include "cima.mm"
include "wne.mm"
include "crab.mm"
include "suppval.mm"
include "ssrab2.mm"
include "syl6eqss.mm"
include "wn.mm"
include "c0.mm"
include "supp0prc.mm"
include "0ss.mm"
include "pm2.61i.mm"

theorem suppssdm
  let cF: class F
  let cZ: class Z
  let vi: setvar i


  assert |- ( F supp Z ) C_ dom F

  proof
    cF
    cvv
    wcel
    cZ
    cvv
    wcel
    wa
    #
    cF
    cZ
    csupp
    co
    #
    cF
    cdm
    #
    wss
    @0
    @1
    cF
    vi
    cv
    csn
    cima
    cZ
    csn
    wne
    #
    vi
    @2
    crab
    @2
    vi
    cvv
    cvv
    cF
    cZ
    suppval
    @3
    vi
    @2
    ssrab2
    syl6eqss
    @0
    wn
    @1
    c0
    @2
    cF
    cZ
    supp0prc
    @2
    0ss
    syl6eqss
    pm2.61i
end
