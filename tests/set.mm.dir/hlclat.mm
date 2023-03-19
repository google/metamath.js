include "chlt.mm"
include "wcel.mm"
include "coml.mm"
include "ccla.mm"
include "clc.mm"
include "hlomcmcv.mm"
include "simp2d.mm"

theorem hlclat
  let cK: class K


  assert |- ( K e. HL -> K e. CLat )

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
    simp2d
end
