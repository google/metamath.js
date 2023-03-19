include "wwe.mm"
include "wse.mm"
include "wa.mm"
include "wn.mm"
include "cvv.mm"
include "cv.mm"
include "wbr.mm"
include "crn.mm"
include "wral.mm"
include "crab.mm"
include "crio.mm"
include "cmpt.mm"
include "crecs.mm"
include "cima.mm"
include "wrex.mm"
include "con0.mm"
include "cres.mm"
include "c0.mm"
include "cif.mm"
include "coi.mm"
include "df-oi.mm"
include "eqtri.mm"
include "iffalse.mm"
include "syl5eq.mm"

theorem oi0
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


  assert |- ( -. ( R We A /\ R Se A ) -> F = (/) )

  proof
    cA
    cR
    wwe
    cA
    cR
    wse
    wa
    #
    wn
    cF
    @0
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
    wral
    vv
    @1
    crio
    cmpt
    crecs
    #
    vz
    cv
    vt
    cv
    cR
    wbr
    vz
    @2
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
    cres
    #
    c0
    cif
    #
    c0
    cF
    cA
    cR
    coi
    @4
    oicl.1
    vx
    vz
    vw
    vv
    vu
    vt
    cA
    cR
    vh
    vj
    df-oi
    eqtri
    @0
    @3
    c0
    iffalse
    syl5eq
end
