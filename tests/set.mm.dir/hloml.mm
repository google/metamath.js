include "chlt.mm"
include "wcel.mm"
include "coml.mm"
include "ccla.mm"
include "clc.mm"
include "hlomcmcv.mm"
include "simp1d.mm"

theorem hloml
  let cK: class K


  assert |- ( K e. HL -> K e. OML )

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
    simp1d
end
