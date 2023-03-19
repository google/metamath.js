include "wwe.mm"
include "wse.mm"
include "wa.mm"
include "wcel.mm"
include "cdm.mm"
include "cfv.mm"
include "wbr.mm"
include "crn.mm"
include "wo.mm"
include "cv.mm"
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
include "ordtypelem7.mm"
include "anasss.mm"

theorem oiiniseg
  let cA: class A
  let cR: class R
  let cF: class F
  let cM: class M
  let cN: class N
  let vt: setvar t
  let vu: setvar u
  let vv: setvar v
  let vx: setvar x
  let vh: setvar h
  let vj: setvar j
  let vw: setvar w
  let vz: setvar z
  let vf: setvar f
  let vi: setvar i
  let vr: setvar r
  let vs: setvar s
  let vy: setvar y
  assume oicl.1: |- F = OrdIso ( R , A )


  assert |- ( ( ( R We A /\ R Se A ) /\ ( N e. A /\ M e. dom F ) ) -> ( ( F ` M ) R N \/ N e. ran F ) )

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
    cN
    cA
    wcel
    cM
    cF
    cdm
    wcel
    cM
    cF
    cfv
    cN
    cR
    wbr
    cN
    cF
    crn
    wcel
    wo
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
    @4
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
    @5
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
    @3
    wral
    vv
    @3
    crio
    cmpt
    #
    cM
    cN
    cF
    vy
    vw
    vv
    vu
    cA
    @3
    cR
    vf
    vh
    vi
    vj
    @7
    crecs
    #
    @7
    vs
    vr
    @8
    eqid
    @3
    eqid
    #
    @7
    eqid
    #
    ordtypecbv
    @9
    @10
    @6
    eqid
    oicl.1
    @0
    @1
    simpl
    @0
    @1
    simpr
    ordtypelem7
    anasss
end
