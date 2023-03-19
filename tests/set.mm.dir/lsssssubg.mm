include "clmod.mm"
include "wcel.mm"
include "csubg.mm"
include "cfv.mm"
include "cv.mm"
include "lsssubg.mm"
include "ex.mm"
include "ssrdv.mm"

theorem lsssssubg
  let cS: class S
  let cW: class W
  let vx: setvar x
  let vy: setvar y
  let cU: class U
  assume lsssubg.s: |- S = ( LSubSp ` W )


  assert |- ( W e. LMod -> S C_ ( SubGrp ` W ) )

  proof
    cW
    clmod
    wcel
    #
    vx
    cS
    cW
    csubg
    cfv
    #
    @0
    vx
    cv
    #
    cS
    wcel
    @2
    @1
    wcel
    cS
    @2
    cW
    lsssubg.s
    lsssubg
    ex
    ssrdv
end
