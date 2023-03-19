include "cvv.mm"
include "cv.mm"
include "ccnv.mm"
include "cn.mm"
include "cima.mm"
include "cfn.mm"
include "wcel.mm"
include "cn0.mm"
include "cmap.mm"
include "co.mm"
include "crab.mm"
include "cbs.mm"
include "cfv.mm"
include "cnx.mm"
include "cop.mm"
include "cplusg.mm"
include "cof.mm"
include "cxp.mm"
include "cres.mm"
include "cmulr.mm"
include "cle.mm"
include "cofr.mm"
include "wbr.mm"
include "cmin.mm"
include "cmpt.mm"
include "cgsu.mm"
include "cmpt2.mm"
include "ctp.mm"
include "csca.mm"
include "cvsca.mm"
include "csn.mm"
include "cts.mm"
include "ctopn.mm"
include "cpt.mm"
include "cun.mm"
include "csb.mm"
include "cmps.mm"
include "df-psr.mm"
include "reldmmpt2.mm"

theorem reldmpsr
  let vh: setvar h
  let vi: setvar i
  let vr: setvar r
  let vy: setvar y
  let vb: setvar b
  let vd: setvar d
  let c.pb: class .+b
  let cJ: class J
  let vf: setvar f
  let vg: setvar g
  let vk: setvar k
  let vx: setvar x
  let wph: wff ph
  let cB: class B
  let cI: class I
  let cR: class R
  let cD: class D
  let c.xp: class .X.
  let c.xb: class .xb


  assert |- Rel dom mPwSer

  proof
    vi
    vr
    cvv
    cvv
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
    vi
    cv
    cmap
    co
    crab
    vb
    vr
    cv
    #
    cbs
    cfv
    #
    vd
    cv
    #
    cmap
    co
    cnx
    cbs
    cfv
    vb
    cv
    #
    cop
    cnx
    cplusg
    cfv
    @0
    cplusg
    cfv
    cof
    @3
    @3
    cxp
    cres
    cop
    cnx
    cmulr
    cfv
    vf
    vg
    @3
    @3
    vk
    @2
    @0
    vx
    vy
    cv
    vk
    cv
    #
    cle
    cofr
    wbr
    vy
    @2
    crab
    vx
    cv
    #
    vf
    cv
    #
    cfv
    @4
    @5
    cmin
    cof
    co
    vg
    cv
    cfv
    @0
    cmulr
    cfv
    #
    co
    cmpt
    cgsu
    co
    cmpt
    cmpt2
    cop
    ctp
    cnx
    csca
    cfv
    @0
    cop
    cnx
    cvsca
    cfv
    vx
    vf
    @1
    @3
    @2
    @5
    csn
    cxp
    @6
    @7
    cof
    co
    cmpt2
    cop
    cnx
    cts
    cfv
    @2
    @0
    ctopn
    cfv
    csn
    cxp
    cpt
    cfv
    cop
    ctp
    cun
    csb
    csb
    cmps
    vx
    vy
    vf
    vg
    vh
    vi
    vk
    vr
    vb
    vd
    df-psr
    reldmmpt2
end
