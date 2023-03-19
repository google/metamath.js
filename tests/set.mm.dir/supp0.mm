include "wcel.mm"
include "c0.mm"
include "csupp.mm"
include "co.mm"
include "cv.mm"
include "csn.mm"
include "cima.mm"
include "wne.mm"
include "cdm.mm"
include "crab.mm"
include "cvv.mm"
include "wceq.mm"
include "0ex.mm"
include "suppval.mm"
include "mpan.mm"
include "dm0.mm"
include "rabeq.mm"
include "mp1i.mm"
include "rab0.mm"
include "a1i.mm"
include "3eqtrd.mm"

theorem supp0
  let cW: class W
  let cZ: class Z
  let vi: setvar i


  assert |- ( Z e. W -> ( (/) supp Z ) = (/) )

  proof
    cZ
    cW
    wcel
    #
    c0
    cZ
    csupp
    co
    #
    c0
    vi
    cv
    csn
    cima
    cZ
    csn
    wne
    #
    vi
    c0
    cdm
    #
    crab
    #
    @2
    vi
    c0
    crab
    #
    c0
    c0
    cvv
    wcel
    @0
    @1
    @4
    wceq
    0ex
    vi
    cvv
    cW
    c0
    cZ
    suppval
    mpan
    @3
    c0
    wceq
    @4
    @5
    wceq
    @0
    dm0
    @2
    vi
    @3
    c0
    rabeq
    mp1i
    @5
    c0
    wceq
    @0
    @2
    vi
    rab0
    a1i
    3eqtrd
end
