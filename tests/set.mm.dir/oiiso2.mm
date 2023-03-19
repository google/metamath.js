include "wwe.mm"
include "wse.mm"
include "wa.mm"
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
include "ordtypelem8.mm"

theorem oiiso2
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


  assert |- ( ( R We A /\ R Se A ) -> F Isom _E , R ( dom F , ran F ) )

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
    @3
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
    @4
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
    @2
    wral
    vv
    @2
    crio
    cmpt
    #
    cF
    vy
    vw
    vv
    vu
    cA
    @2
    cR
    vf
    vh
    vi
    vj
    @6
    crecs
    #
    @6
    vs
    vr
    @7
    eqid
    @2
    eqid
    #
    @6
    eqid
    #
    ordtypecbv
    @8
    @9
    @5
    eqid
    oicl.1
    @0
    @1
    simpl
    @0
    @1
    simpr
    ordtypelem8
end
