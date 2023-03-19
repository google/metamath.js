include "cvv.mm"
include "cv.mm"
include "cmpl.mm"
include "co.mm"
include "cbs.mm"
include "cfv.mm"
include "c0g.mm"
include "csupp.mm"
include "ccnfld.mm"
include "cgsu.mm"
include "cmpt.mm"
include "crn.mm"
include "cxr.mm"
include "clt.mm"
include "csup.mm"
include "cmdg.mm"
include "df-mdeg.mm"
include "reldmmpt2.mm"

theorem reldmmdeg
  let vi: setvar i
  let vr: setvar r
  let vh: setvar h
  let vf: setvar f


  assert |- Rel dom mDeg

  proof
    vi
    vr
    cvv
    cvv
    vf
    vi
    cv
    vr
    cv
    #
    cmpl
    co
    cbs
    cfv
    vh
    vf
    cv
    @0
    c0g
    cfv
    csupp
    co
    ccnfld
    vh
    cv
    cgsu
    co
    cmpt
    crn
    cxr
    clt
    csup
    cmpt
    cmdg
    vf
    vh
    vi
    vr
    df-mdeg
    reldmmpt2
end
