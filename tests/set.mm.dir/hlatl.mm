include "chlt.mm"
include "wcel.mm"
include "clc.mm"
include "cal.mm"
include "hlcvl.mm"
include "cvlatl.mm"
include "syl.mm"

theorem hlatl
  let cK: class K


  assert |- ( K e. HL -> K e. AtLat )

  proof
    cK
    chlt
    wcel
    cK
    clc
    wcel
    cK
    cal
    wcel
    cK
    hlcvl
    cK
    cvlatl
    syl
end
