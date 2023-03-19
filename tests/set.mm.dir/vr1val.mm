include "cvv.mm"
include "wcel.mm"
include "c0.mm"
include "c1o.mm"
include "cmvr.mm"
include "co.mm"
include "cfv.mm"
include "wceq.mm"
include "cv1.mm"
include "cv.mm"
include "oveq2.mm"
include "fveq1d.mm"
include "df-vr1.mm"
include "fvex.mm"
include "fvmpt.mm"
include "syl5eq.mm"
include "wn.mm"
include "fvprc.mm"
include "0fv.mm"
include "3eqtr4g.mm"
include "ccnv.mm"
include "cn.mm"
include "cima.mm"
include "cfn.mm"
include "cn0.mm"
include "cmap.mm"
include "crab.mm"
include "c1.mm"
include "cc0.mm"
include "cif.mm"
include "cmpt.mm"
include "cur.mm"
include "c0g.mm"
include "df-mvr.mm"
include "reldmmpt2.mm"
include "ovprc2.mm"
include "eqtr4d.mm"
include "pm2.61i.mm"

theorem vr1val
  let cR: class R
  let cX: class X
  let vf: setvar f
  let vh: setvar h
  let vi: setvar i
  let vr: setvar r
  let vx: setvar x
  let vy: setvar y
  assume vr1val.1: |- X = ( var1 ` R )


  assert |- X = ( ( 1o mVar R ) ` (/) )

  proof
    cR
    cvv
    wcel
    #
    cX
    c0
    c1o
    cR
    cmvr
    co
    #
    cfv
    #
    wceq
    @0
    cX
    cR
    cv1
    cfv
    #
    @2
    vr1val.1
    vr
    cR
    c0
    c1o
    vr
    cv
    #
    cmvr
    co
    #
    cfv
    @2
    cvv
    cv1
    @4
    cR
    wceq
    c0
    @5
    @1
    @4
    cR
    c1o
    cmvr
    oveq2
    fveq1d
    vr
    df-vr1
    c0
    @1
    fvex
    fvmpt
    syl5eq
    @0
    wn
    #
    cX
    c0
    c0
    cfv
    #
    @2
    @6
    @3
    c0
    cX
    @7
    cR
    cv1
    fvprc
    vr1val.1
    c0
    0fv
    3eqtr4g
    @6
    c0
    @1
    c0
    c1o
    cR
    cmvr
    vi
    vr
    cvv
    cvv
    vx
    vi
    cv
    #
    vf
    vh
    cv
    ccnv
    cn
    cima
    cfn
    wcel
    vh
    cn0
    @8
    cmap
    co
    crab
    vf
    cv
    vy
    @8
    vy
    cv
    vx
    cv
    wceq
    c1
    cc0
    cif
    cmpt
    wceq
    @4
    cur
    cfv
    @4
    c0g
    cfv
    cif
    cmpt
    cmpt
    cmvr
    vx
    vy
    vf
    vh
    vi
    vr
    df-mvr
    reldmmpt2
    ovprc2
    fveq1d
    eqtr4d
    pm2.61i
end
