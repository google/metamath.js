include "cvv.mm"
include "ccrg.mm"
include "cv.mm"
include "cbs.mm"
include "cfv.mm"
include "csubrg.mm"
include "cress.mm"
include "co.mm"
include "cmpl.mm"
include "cascl.mm"
include "ccom.mm"
include "cmap.mm"
include "csn.mm"
include "cxp.mm"
include "cmpt.mm"
include "wceq.mm"
include "cmvr.mm"
include "wa.mm"
include "cpws.mm"
include "crh.mm"
include "crio.mm"
include "csb.mm"
include "ces.mm"
include "df-evls.mm"
include "reldmmpt2.mm"

theorem reldmevls
  let va: setvar a
  let vb: setvar b
  let vf: setvar f
  let vg: setvar g
  let vi: setvar i
  let vr: setvar r
  let vs: setvar s
  let vw: setvar w
  let vx: setvar x
  let cI: class I
  let cS: class S


  assert |- Rel dom evalSub

  proof
    vi
    vs
    cvv
    ccrg
    vb
    vs
    cv
    #
    cbs
    cfv
    vr
    @0
    csubrg
    cfv
    vw
    vi
    cv
    #
    @0
    vr
    cv
    #
    cress
    co
    #
    cmpl
    co
    vf
    cv
    #
    vw
    cv
    #
    cascl
    cfv
    ccom
    vx
    @2
    vb
    cv
    @1
    cmap
    co
    #
    vx
    cv
    #
    csn
    cxp
    cmpt
    wceq
    @4
    @1
    @3
    cmvr
    co
    ccom
    vx
    @1
    vg
    @6
    @7
    vg
    cv
    cfv
    cmpt
    cmpt
    wceq
    wa
    vf
    @5
    @0
    @6
    cpws
    co
    crh
    co
    crio
    csb
    cmpt
    csb
    ces
    vx
    vw
    vf
    vg
    vi
    vs
    vr
    vb
    df-evls
    reldmmpt2
end
