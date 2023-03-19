include "cvv.mm"
include "cv.mm"
include "cbs.mm"
include "cfv.mm"
include "cxp.mm"
include "c1st.mm"
include "chom.mm"
include "co.mm"
include "c2nd.mm"
include "cmpt2.mm"
include "cnx.mm"
include "cop.mm"
include "cco.mm"
include "ctp.mm"
include "csb.mm"
include "cxpc.mm"
include "df-xpc.mm"
include "tpex.mm"
include "csbex.mm"
include "fnmpt2i.mm"

theorem fnxpc
  let vb: setvar b
  let vf: setvar f
  let vg: setvar g
  let vh: setvar h
  let vr: setvar r
  let vs: setvar s
  let vu: setvar u
  let vv: setvar v
  let vx: setvar x
  let vy: setvar y


  assert |- Xc. Fn ( _V X. _V )

  proof
    vr
    vs
    cvv
    cvv
    vb
    vr
    cv
    #
    cbs
    cfv
    vs
    cv
    #
    cbs
    cfv
    cxp
    #
    vh
    vu
    vv
    vb
    cv
    #
    @3
    vu
    cv
    #
    c1st
    cfv
    vv
    cv
    #
    c1st
    cfv
    @0
    chom
    cfv
    co
    @4
    c2nd
    cfv
    @5
    c2nd
    cfv
    @1
    chom
    cfv
    co
    cxp
    cmpt2
    #
    cnx
    cbs
    cfv
    @3
    cop
    #
    cnx
    chom
    cfv
    vh
    cv
    #
    cop
    #
    cnx
    cco
    cfv
    vx
    vy
    @3
    @3
    cxp
    @3
    vg
    vf
    vx
    cv
    #
    c2nd
    cfv
    #
    vy
    cv
    #
    @8
    co
    @10
    @8
    cfv
    vg
    cv
    #
    c1st
    cfv
    vf
    cv
    #
    c1st
    cfv
    @10
    c1st
    cfv
    #
    c1st
    cfv
    @11
    c1st
    cfv
    cop
    @12
    c1st
    cfv
    @0
    cco
    cfv
    co
    co
    @13
    c2nd
    cfv
    @14
    c2nd
    cfv
    @15
    c2nd
    cfv
    @11
    c2nd
    cfv
    cop
    @12
    c2nd
    cfv
    @1
    cco
    cfv
    co
    co
    cop
    cmpt2
    cmpt2
    cop
    #
    ctp
    #
    csb
    #
    csb
    cxpc
    vx
    vy
    vv
    vu
    vf
    vg
    vh
    vs
    vr
    vb
    df-xpc
    vb
    @2
    @18
    vh
    @6
    @17
    @7
    @9
    @16
    tpex
    csbex
    csbex
    fnmpt2i
end
