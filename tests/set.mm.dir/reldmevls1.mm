include "cvv.mm"
include "cv.mm"
include "cbs.mm"
include "cfv.mm"
include "cpw.mm"
include "c1o.mm"
include "cmap.mm"
include "co.mm"
include "csn.mm"
include "cxp.mm"
include "cmpt.mm"
include "ccom.mm"
include "ces.mm"
include "csb.mm"
include "ces1.mm"
include "df-evls1.mm"
include "reldmmpt2.mm"

theorem reldmevls1
  let vb: setvar b
  let vr: setvar r
  let vs: setvar s
  let vx: setvar x
  let vy: setvar y


  assert |- Rel dom evalSub1

  proof
    vs
    vr
    cvv
    vs
    cv
    #
    cbs
    cfv
    #
    cpw
    vb
    @1
    vx
    vb
    cv
    #
    @2
    c1o
    cmap
    co
    cmap
    co
    vx
    cv
    vy
    @2
    c1o
    vy
    cv
    csn
    cxp
    cmpt
    ccom
    cmpt
    vr
    cv
    c1o
    @0
    ces
    co
    cfv
    ccom
    csb
    ces1
    vx
    vy
    vs
    vr
    vb
    df-evls1
    reldmmpt2
end
