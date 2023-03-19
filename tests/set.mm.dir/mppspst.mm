include "cv.mm"
include "cotp.mm"
include "wcel.mm"
include "cmcls.mm"
include "cfv.mm"
include "co.mm"
include "wa.mm"
include "coprab.mm"
include "eqid.mm"
include "mppsval.mm"
include "mppspstlem.mm"
include "eqsstri.mm"

theorem mppspst
  let cP: class P
  let cT: class T
  let cJ: class J
  let va: setvar a
  let vd: setvar d
  let vh: setvar h
  let cA: class A
  let vt: setvar t
  let vx: setvar x
  let cC: class C
  let cD: class D
  let cH: class H
  assume mppsval.p: |- P = ( mPreSt ` T )
  assume mppsval.j: |- J = ( mPPSt ` T )


  assert |- J C_ P

  proof
    cJ
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
    cP
    wcel
    @2
    @0
    @1
    cT
    cmcls
    cfv
    #
    co
    wcel
    wa
    vd
    vh
    va
    coprab
    cP
    @3
    cP
    cT
    vh
    cJ
    va
    vd
    mppsval.p
    mppsval.j
    @3
    eqid
    #
    mppsval
    @3
    cP
    cT
    vh
    cJ
    va
    vd
    mppsval.p
    mppsval.j
    @4
    mppspstlem
    eqsstri
end
