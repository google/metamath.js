include "cslmd.mm"
include "wcel.mm"
include "ccmn.mm"
include "cmnd.mm"
include "slmdcmn.mm"
include "cmnmnd.mm"
include "syl.mm"

theorem slmdmnd
  let cW: class W
  let vw: setvar w
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cF: class F


  assert |- ( W e. SLMod -> W e. Mnd )

  proof
    cW
    cslmd
    wcel
    cW
    ccmn
    wcel
    cW
    cmnd
    wcel
    cW
    slmdcmn
    cW
    cmnmnd
    syl
end
