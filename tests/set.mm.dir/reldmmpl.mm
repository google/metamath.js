include "cvv.mm"
include "cv.mm"
include "cmps.mm"
include "co.mm"
include "c0g.mm"
include "cfv.mm"
include "cfsupp.mm"
include "wbr.mm"
include "cbs.mm"
include "crab.mm"
include "cress.mm"
include "csb.mm"
include "cmpl.mm"
include "df-mpl.mm"
include "reldmmpt2.mm"

theorem reldmmpl
  let cB: class B
  let vf: setvar f
  let vi: setvar i
  let vr: setvar r
  let vs: setvar s
  let cI: class I
  let cR: class R
  let cS: class S
  let cU: class U
  let cX: class X
  let c.0: class .0.


  assert |- Rel dom mPoly

  proof
    vi
    vr
    cvv
    cvv
    vs
    vi
    cv
    vr
    cv
    #
    cmps
    co
    vs
    cv
    #
    vf
    cv
    @0
    c0g
    cfv
    cfsupp
    wbr
    vf
    @1
    cbs
    cfv
    crab
    cress
    co
    csb
    cmpl
    vs
    vf
    vi
    vr
    df-mpl
    reldmmpt2
end
