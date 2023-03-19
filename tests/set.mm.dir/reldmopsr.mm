include "cvv.mm"
include "cv.mm"
include "cxp.mm"
include "cpw.mm"
include "cmps.mm"
include "co.mm"
include "cnx.mm"
include "cple.mm"
include "cfv.mm"
include "cpr.mm"
include "cbs.mm"
include "wss.mm"
include "cplt.mm"
include "wbr.mm"
include "cltb.mm"
include "wceq.mm"
include "wi.mm"
include "wral.mm"
include "wa.mm"
include "wrex.mm"
include "ccnv.mm"
include "cn.mm"
include "cima.mm"
include "cfn.mm"
include "wcel.mm"
include "cn0.mm"
include "cmap.mm"
include "crab.mm"
include "wsbc.mm"
include "wo.mm"
include "copab.mm"
include "cop.mm"
include "csts.mm"
include "csb.mm"
include "cmpt.mm"
include "copws.mm"
include "df-opsr.mm"
include "reldmmpt2.mm"

theorem reldmopsr
  let c.le: class .<_
  let vr: setvar r
  let vi: setvar i
  let vp: setvar p
  let vs: setvar s
  let cB: class B
  let vd: setvar d
  let vh: setvar h
  let vw: setvar w
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cI: class I
  let wph: wff ph
  let c.lt: class .<
  let cD: class D
  let cS: class S
  let cT: class T
  let cR: class R


  assert |- Rel dom ordPwSer

  proof
    vi
    vs
    cvv
    cvv
    vr
    vi
    cv
    #
    @0
    cxp
    cpw
    vp
    @0
    vs
    cv
    #
    cmps
    co
    vp
    cv
    #
    cnx
    cple
    cfv
    vx
    cv
    #
    vy
    cv
    #
    cpr
    @2
    cbs
    cfv
    wss
    vz
    cv
    #
    @3
    cfv
    @5
    @4
    cfv
    @1
    cplt
    cfv
    wbr
    vw
    cv
    #
    @5
    vr
    cv
    @0
    cltb
    co
    wbr
    @6
    @3
    cfv
    @6
    @4
    cfv
    wceq
    wi
    vw
    vd
    cv
    #
    wral
    wa
    vz
    @7
    wrex
    vd
    vh
    cv
    ccnv
    cn
    cima
    cfn
    wcel
    vh
    cn0
    @0
    cmap
    co
    crab
    wsbc
    @3
    @4
    wceq
    wo
    wa
    vx
    vy
    copab
    cop
    csts
    co
    csb
    cmpt
    copws
    vx
    vy
    vz
    vw
    vh
    vi
    vs
    vr
    vp
    vd
    df-opsr
    reldmmpt2
end
