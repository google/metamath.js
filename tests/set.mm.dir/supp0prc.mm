include "cv.mm"
include "csn.mm"
include "cima.mm"
include "wne.mm"
include "cdm.mm"
include "crab.mm"
include "csupp.mm"
include "cvv.mm"
include "df-supp.mm"
include "mpt2ndm0.mm"

theorem supp0prc
  let cX: class X
  let cZ: class Z
  let cV: class V
  let vx: setvar x
  let vz: setvar z
  let cW: class W
  let vi: setvar i


  assert |- ( -. ( X e. _V /\ Z e. _V ) -> ( X supp Z ) = (/) )

  proof
    vx
    vz
    vx
    cv
    #
    vi
    cv
    csn
    cima
    vz
    cv
    csn
    wne
    vi
    @0
    cdm
    crab
    csupp
    cX
    cZ
    cvv
    cvv
    vx
    vz
    vi
    df-supp
    mpt2ndm0
end
