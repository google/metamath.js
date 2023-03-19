include "wcel.mm"
include "crn.mm"
include "cv.mm"
include "cdom.mm"
include "wbr.mm"
include "con0.mm"
include "crab.mm"
include "cvv.mm"
include "cdm.mm"
include "cxp.mm"
include "cpw.mm"
include "wss.mm"
include "wfun.mm"
include "wceq.mm"
include "wi.mm"
include "hartogslem1.mm"
include "simp3i.mm"
include "simp2i.mm"
include "simp1i.mm"
include "sqxpexg.mm"
include "pwexg.mm"
include "syl.mm"
include "ssexg.mm"
include "sylancr.mm"
include "funex.mm"
include "rnexg.mm"
include "eqeltrrd.mm"

theorem hartogslem2
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vw: setvar w
  let vt: setvar t
  let cA: class A
  let cR: class R
  let vf: setvar f
  let cF: class F
  let cV: class V
  let vs: setvar s
  let vr: setvar r
  assume hartogslem.2: |- F = { <. r , y >. | ( ( ( dom r C_ A /\ ( _I |` dom r ) C_ r /\ r C_ ( dom r X. dom r ) ) /\ ( r \ _I ) We dom r ) /\ y = dom OrdIso ( ( r \ _I ) , dom r ) ) }
  assume hartogslem.3: |- R = { <. s , t >. | E. w e. y E. z e. y ( ( s = ( f ` w ) /\ t = ( f ` z ) ) /\ w _E z ) }

  disjoint f s
  disjoint f t
  disjoint f w
  disjoint f y
  disjoint f z
  disjoint s t
  disjoint s w
  disjoint s y
  disjoint s z
  disjoint t w
  disjoint t y
  disjoint t z
  disjoint w y
  disjoint w z
  disjoint y z
  disjoint f r
  disjoint f x
  disjoint A f
  disjoint r x
  disjoint r y
  disjoint A r
  disjoint x y
  disjoint A x
  disjoint A y
  disjoint R r
  disjoint R x
  disjoint V r
  disjoint V y
  assert |- ( A e. V -> { x e. On | x ~<_ A } e. _V )

  proof
    cA
    cV
    wcel
    #
    cF
    crn
    #
    vx
    cv
    cA
    cdom
    wbr
    vx
    con0
    crab
    #
    cvv
    cF
    cdm
    #
    cA
    cA
    cxp
    #
    cpw
    #
    wss
    #
    cF
    wfun
    #
    @0
    @1
    @2
    wceq
    wi
    #
    vx
    vy
    vz
    vw
    vt
    cA
    cR
    vf
    cF
    cV
    vs
    vr
    hartogslem.2
    hartogslem.3
    hartogslem1
    #
    simp3i
    @0
    cF
    cvv
    wcel
    #
    @1
    cvv
    wcel
    @0
    @7
    @3
    cvv
    wcel
    #
    @10
    @6
    @7
    @8
    @9
    simp2i
    @0
    @6
    @5
    cvv
    wcel
    #
    @11
    @6
    @7
    @8
    @9
    simp1i
    @0
    @4
    cvv
    wcel
    @12
    cA
    cV
    sqxpexg
    @4
    cvv
    pwexg
    syl
    @3
    @5
    cvv
    ssexg
    sylancr
    cvv
    cF
    funex
    sylancr
    cF
    cvv
    rnexg
    syl
    eqeltrrd
end
