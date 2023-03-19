include "cv.mm"
include "cbs.mm"
include "cfv.mm"
include "wf.mm"
include "cxp.mm"
include "c1st.mm"
include "c2nd.mm"
include "chom.mm"
include "co.mm"
include "cmap.mm"
include "cixp.mm"
include "wcel.mm"
include "ccid.mm"
include "wceq.mm"
include "cop.mm"
include "cco.mm"
include "wral.mm"
include "wa.mm"
include "w3a.mm"
include "wsbc.mm"
include "ccat.mm"
include "cfunc.mm"
include "df-func.mm"
include "relmpt2opab.mm"

theorem relfunc
  let cD: class D
  let cE: class E
  let vb: setvar b
  let vf: setvar f
  let vg: setvar g
  let vh: setvar h
  let vm: setvar m
  let vn: setvar n
  let vt: setvar t
  let vu: setvar u
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z


  assert |- Rel ( D Func E )

  proof
    vb
    cv
    #
    vu
    cv
    #
    cbs
    cfv
    vf
    cv
    #
    wf
    vg
    cv
    #
    vz
    @0
    @0
    cxp
    vz
    cv
    #
    c1st
    cfv
    @2
    cfv
    @4
    c2nd
    cfv
    @2
    cfv
    @1
    chom
    cfv
    co
    @4
    vt
    cv
    #
    chom
    cfv
    #
    cfv
    cmap
    co
    cixp
    wcel
    vx
    cv
    #
    @5
    ccid
    cfv
    cfv
    @7
    @7
    @3
    co
    cfv
    @7
    @2
    cfv
    #
    @1
    ccid
    cfv
    cfv
    wceq
    vn
    cv
    #
    vm
    cv
    #
    @7
    vy
    cv
    #
    cop
    @4
    @5
    cco
    cfv
    co
    co
    @7
    @4
    @3
    co
    cfv
    @9
    @11
    @4
    @3
    co
    cfv
    @10
    @7
    @11
    @3
    co
    cfv
    @8
    @11
    @2
    cfv
    cop
    @4
    @2
    cfv
    @1
    cco
    cfv
    co
    co
    wceq
    vn
    @11
    @4
    @6
    co
    wral
    vm
    @7
    @11
    @6
    co
    wral
    vz
    @0
    wral
    vy
    @0
    wral
    wa
    vx
    @0
    wral
    w3a
    vb
    @5
    cbs
    cfv
    wsbc
    vt
    vu
    vf
    vg
    ccat
    ccat
    cD
    cE
    cfunc
    vx
    vy
    vz
    vu
    vt
    vf
    vg
    vm
    vn
    vb
    df-func
    relmpt2opab
end
