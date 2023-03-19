include "ccat.mm"
include "cnx.mm"
include "cbs.mm"
include "cfv.mm"
include "cv.mm"
include "cfunc.mm"
include "co.mm"
include "cop.mm"
include "chom.mm"
include "cnat.mm"
include "cco.mm"
include "cxp.mm"
include "c1st.mm"
include "c2nd.mm"
include "cmpt.mm"
include "cmpt2.mm"
include "csb.mm"
include "ctp.mm"
include "cfuc.mm"
include "df-fuc.mm"
include "tpex.mm"
include "fnmpt2i.mm"

theorem fnfuc
  let va: setvar a
  let vb: setvar b
  let vf: setvar f
  let vg: setvar g
  let vh: setvar h
  let vr: setvar r
  let vs: setvar s
  let vt: setvar t
  let vu: setvar u
  let vv: setvar v
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let cC: class C
  let cF: class F
  let cJ: class J
  let cG: class G
  let cH: class H
  let wph: wff ph
  let cK: class K
  let cL: class L
  let c.x: class .x.
  let cD: class D


  assert |- FuncCat Fn ( Cat X. Cat )

  proof
    vt
    vu
    ccat
    ccat
    cnx
    cbs
    cfv
    vt
    cv
    #
    vu
    cv
    #
    cfunc
    co
    #
    cop
    #
    cnx
    chom
    cfv
    @0
    @1
    cnat
    co
    #
    cop
    #
    cnx
    cco
    cfv
    vv
    vh
    @2
    @2
    cxp
    @2
    vf
    vv
    cv
    #
    c1st
    cfv
    vg
    @6
    c2nd
    cfv
    vb
    va
    vg
    cv
    #
    vh
    cv
    #
    @4
    co
    vf
    cv
    #
    @7
    @4
    co
    vx
    @0
    cbs
    cfv
    vx
    cv
    #
    vb
    cv
    cfv
    @10
    va
    cv
    cfv
    @10
    @9
    c1st
    cfv
    cfv
    @10
    @7
    c1st
    cfv
    cfv
    cop
    @10
    @8
    c1st
    cfv
    cfv
    @1
    cco
    cfv
    co
    co
    cmpt
    cmpt2
    csb
    csb
    cmpt2
    cop
    #
    ctp
    cfuc
    vx
    vv
    vu
    vt
    vf
    vg
    vh
    va
    vb
    df-fuc
    @3
    @5
    @11
    tpex
    fnmpt2i
end
