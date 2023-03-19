include "wwe.mm"
include "wse.mm"
include "cvv.mm"
include "wcel.mm"
include "w3a.mm"
include "cv.mm"
include "wbr.mm"
include "crn.mm"
include "wral.mm"
include "crab.mm"
include "wn.mm"
include "crio.mm"
include "cmpt.mm"
include "crecs.mm"
include "cima.mm"
include "wrex.mm"
include "con0.mm"
include "eqid.mm"
include "ordtypecbv.mm"
include "simp1.mm"
include "simp2.mm"
include "simp3.mm"
include "ordtypelem9.mm"

theorem ordtype2
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


  assert |- ( ( R We A /\ R Se A /\ F e. _V ) -> F Isom _E , R ( dom F , A ) )

  proof
    cA
    cR
    wwe
    #
    cA
    cR
    wse
    #
    cF
    cvv
    wcel
    #
    w3a
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
    @2
    simp1
    @0
    @1
    @2
    simp2
    @0
    @1
    @2
    simp3
    ordtypelem9
end
