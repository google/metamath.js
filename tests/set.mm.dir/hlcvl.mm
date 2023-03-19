include "chlt.mm"
include "wcel.mm"
include "coml.mm"
include "ccla.mm"
include "clc.mm"
include "hlomcmcv.mm"
include "simp3d.mm"

theorem hlcvl
  let cK: class K


  assert |- ( K e. HL -> K e. CvLat )

  proof
    cK
    chlt
    wcel
    cK
    coml
    wcel
    cK
    ccla
    wcel
    cK
    clc
    wcel
    cK
    hlomcmcv
    simp3d
end
