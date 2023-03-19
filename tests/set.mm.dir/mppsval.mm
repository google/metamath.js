include "cmpps.mm"
include "cfv.mm"
include "cv.mm"
include "cotp.mm"
include "wcel.mm"
include "co.mm"
include "wa.mm"
include "coprab.mm"
include "cvv.mm"
include "wceq.mm"
include "cmpst.mm"
include "cmcls.mm"
include "fveq2.mm"
include "syl6eqr.mm"
include "eleq2d.mm"
include "oveqd.mm"
include "anbi12d.mm"
include "oprabbidv.mm"
include "df-mpps.mm"
include "fvex.mm"
include "eqeltri.mm"
include "mppspstlem.mm"
include "ssexi.mm"
include "fvmpt.mm"
include "wn.mm"
include "c0.mm"
include "fvprc.mm"
include "cop.mm"
include "wex.mm"
include "cab.mm"
include "df-oprab.mm"
include "wne.mm"
include "abn0.mm"
include "elfvex.mm"
include "eleq2s.mm"
include "ad2antrl.mm"
include "exlimivv.mm"
include "sylbi.mm"
include "necon1bi.mm"
include "syl5eq.mm"
include "eqtr4d.mm"
include "pm2.61i.mm"
include "eqtri.mm"

theorem mppsval
  let cC: class C
  let cP: class P
  let cT: class T
  let vh: setvar h
  let cJ: class J
  let va: setvar a
  let vd: setvar d
  let cA: class A
  let vt: setvar t
  let vx: setvar x
  let cD: class D
  let cH: class H
  assume mppsval.p: |- P = ( mPreSt ` T )
  assume mppsval.j: |- J = ( mPPSt ` T )
  assume mppsval.c: |- C = ( mCls ` T )

  disjoint a d
  disjoint a h
  disjoint d h
  disjoint C a
  disjoint C d
  disjoint C h
  disjoint P a
  disjoint P d
  disjoint P h
  disjoint T a
  disjoint T d
  disjoint T h
  disjoint A a
  disjoint A d
  disjoint A h
  disjoint a t
  disjoint a x
  disjoint d t
  disjoint d x
  disjoint h t
  disjoint h x
  disjoint t x
  disjoint C t
  disjoint C x
  disjoint P t
  disjoint P x
  disjoint T t
  disjoint T x
  disjoint D a
  disjoint D d
  disjoint D h
  disjoint H a
  disjoint H d
  disjoint H h
  assert |- J = { <. <. d , h >. , a >. | ( <. d , h , a >. e. P /\ a e. ( d C h ) ) }

  proof
    cJ
    cT
    cmpps
    cfv
    #
    vd
    cv
    #
    vh
    cv
    #
    va
    cv
    #
    cotp
    #
    cP
    wcel
    #
    @3
    @1
    @2
    cC
    co
    #
    wcel
    #
    wa
    #
    vd
    vh
    va
    coprab
    #
    mppsval.j
    cT
    cvv
    wcel
    #
    @0
    @9
    wceq
    vt
    cT
    @4
    vt
    cv
    #
    cmpst
    cfv
    #
    wcel
    #
    @3
    @1
    @2
    @11
    cmcls
    cfv
    #
    co
    #
    wcel
    #
    wa
    #
    vd
    vh
    va
    coprab
    @9
    cvv
    cmpps
    @11
    cT
    wceq
    #
    @17
    @8
    vd
    vh
    va
    @18
    @13
    @5
    @16
    @7
    @18
    @12
    cP
    @4
    @18
    @12
    cT
    cmpst
    cfv
    #
    cP
    @11
    cT
    cmpst
    fveq2
    mppsval.p
    syl6eqr
    eleq2d
    @18
    @15
    @6
    @3
    @18
    @14
    cC
    @1
    @2
    @18
    @14
    cT
    cmcls
    cfv
    cC
    @11
    cT
    cmcls
    fveq2
    mppsval.c
    syl6eqr
    oveqd
    eleq2d
    anbi12d
    oprabbidv
    vt
    vh
    va
    vd
    df-mpps
    @9
    cP
    cP
    @19
    cvv
    mppsval.p
    cT
    cmpst
    fvex
    eqeltri
    cC
    cP
    cT
    vh
    cJ
    va
    vd
    mppsval.p
    mppsval.j
    mppsval.c
    mppspstlem
    ssexi
    fvmpt
    @10
    wn
    #
    @0
    c0
    @9
    cT
    cmpps
    fvprc
    @20
    @9
    vx
    cv
    @1
    @2
    cop
    @3
    cop
    wceq
    #
    @8
    wa
    #
    va
    wex
    vh
    wex
    #
    vd
    wex
    #
    vx
    cab
    #
    c0
    @8
    vd
    vh
    va
    vx
    df-oprab
    @10
    @25
    c0
    @25
    c0
    wne
    @24
    vx
    wex
    @10
    @24
    vx
    abn0
    @23
    @10
    vx
    vd
    @22
    @10
    vh
    va
    @5
    @10
    @21
    @7
    @10
    @4
    @19
    cP
    @4
    cT
    cmpst
    elfvex
    mppsval.p
    eleq2s
    ad2antrl
    exlimivv
    exlimivv
    sylbi
    necon1bi
    syl5eq
    eqtr4d
    pm2.61i
    eqtri
end
