include "cv.mm"
include "cxp.mm"
include "wfn.mm"
include "cfv.mm"
include "cpw.mm"
include "cixp.mm"
include "wcel.mm"
include "wrex.mm"
include "wa.mm"
include "wex.mm"
include "cssc.mm"
include "df-ssc.mm"
include "relopabi.mm"

theorem sscrel
  let vc: setvar c
  let vf: setvar f
  let vg: setvar g
  let vh: setvar h
  let vj: setvar j
  let vs: setvar s
  let vt: setvar t
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cH: class H
  let cJ: class J


  assert |- Rel C_cat

  proof
    vj
    cv
    #
    vt
    cv
    #
    @1
    cxp
    wfn
    vh
    cv
    vx
    vs
    cv
    #
    @2
    cxp
    vx
    cv
    @0
    cfv
    cpw
    cixp
    wcel
    vs
    @1
    cpw
    wrex
    wa
    vt
    wex
    vh
    vj
    cssc
    vx
    vt
    vh
    vj
    vs
    df-ssc
    relopabi
end
