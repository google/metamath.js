include "cfrlm.mm"
include "cvv.mm"
include "cv.mm"
include "crglmod.mm"
include "cfv.mm"
include "csn.mm"
include "cxp.mm"
include "cdsmm.mm"
include "co.mm"
include "df-frlm.mm"
include "reldmmpt2.mm"
include "strov2rcl.mm"

theorem frlmrcl
  let cB: class B
  let cR: class R
  let cF: class F
  let cI: class I
  let cX: class X
  let vr: setvar r
  let vi: setvar i
  let cW: class W
  assume frlmval.f: |- F = ( R freeLMod I )
  assume frlmrcl.b: |- B = ( Base ` F )


  assert |- ( X e. B -> R e. _V )

  proof
    cB
    cI
    cF
    cfrlm
    cR
    cX
    frlmval.f
    frlmrcl.b
    vr
    vi
    cvv
    cvv
    vr
    cv
    #
    vi
    cv
    @0
    crglmod
    cfv
    csn
    cxp
    cdsmm
    co
    cfrlm
    vi
    vr
    df-frlm
    reldmmpt2
    strov2rcl
end
