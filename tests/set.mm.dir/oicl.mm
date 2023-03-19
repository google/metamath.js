include "wwe.mm"
include "wse.mm"
include "wa.mm"
include "cdm.mm"
include "word.mm"
include "wf.mm"
include "cv.mm"
include "wbr.mm"
include "crn.mm"
include "wral.mm"
include "crab.mm"
include "cvv.mm"
include "wn.mm"
include "crio.mm"
include "cmpt.mm"
include "crecs.mm"
include "cima.mm"
include "wrex.mm"
include "con0.mm"
include "eqid.mm"
include "ordtypecbv.mm"
include "simpl.mm"
include "simpr.mm"
include "ordtypelem5.mm"
include "simpld.mm"
include "c0.mm"
include "ord0.mm"
include "wceq.mm"
include "wb.mm"
include "oi0.mm"
include "dmeqd.mm"
include "dm0.mm"
include "syl6eq.mm"
include "ordeq.mm"
include "syl.mm"
include "mpbiri.mm"
include "pm2.61i.mm"

theorem oicl
  let cA: class A
  let cR: class R
  let cF: class F
  let vt: setvar t
  let vu: setvar u
  let vv: setvar v
  let vx: setvar x
  let vh: setvar h
  let vj: setvar j
  let vw: setvar w
  let vz: setvar z
  let cM: class M
  let vf: setvar f
  let vi: setvar i
  let vr: setvar r
  let vs: setvar s
  let vy: setvar y
  let cN: class N
  assume oicl.1: |- F = OrdIso ( R , A )


  assert |- Ord dom F

  proof
    cA
    cR
    wwe
    #
    cA
    cR
    wse
    #
    wa
    #
    cF
    cdm
    #
    word
    #
    @2
    @4
    @3
    cA
    cF
    wf
    @2
    vx
    vz
    vw
    vv
    vu
    vt
    cA
    vj
    cv
    vw
    cv
    cR
    wbr
    vj
    vh
    cv
    crn
    wral
    vw
    cA
    crab
    #
    cR
    vz
    cv
    vt
    cv
    cR
    wbr
    vz
    vf
    cvv
    vr
    cv
    vs
    cv
    cR
    wbr
    wn
    vr
    vi
    cv
    vy
    cv
    cR
    wbr
    vi
    vf
    cv
    crn
    wral
    vy
    cA
    crab
    #
    wral
    vs
    @6
    crio
    cmpt
    crecs
    #
    vx
    cv
    cima
    wral
    vt
    cA
    wrex
    vx
    con0
    crab
    #
    vh
    vj
    @7
    vh
    cvv
    vu
    cv
    vv
    cv
    cR
    wbr
    wn
    vu
    @5
    wral
    vv
    @5
    crio
    cmpt
    #
    cF
    vy
    vw
    vv
    vu
    cA
    @5
    cR
    vf
    vh
    vi
    vj
    @9
    crecs
    #
    @9
    vs
    vr
    @10
    eqid
    @5
    eqid
    #
    @9
    eqid
    #
    ordtypecbv
    @11
    @12
    @8
    eqid
    oicl.1
    @0
    @1
    simpl
    @0
    @1
    simpr
    ordtypelem5
    simpld
    @2
    wn
    #
    @4
    c0
    word
    #
    ord0
    @13
    @3
    c0
    wceq
    @4
    @14
    wb
    @13
    @3
    c0
    cdm
    c0
    @13
    cF
    c0
    cA
    cR
    cF
    oicl.1
    oi0
    dmeqd
    dm0
    syl6eq
    @3
    c0
    ordeq
    syl
    mpbiri
    pm2.61i
end
