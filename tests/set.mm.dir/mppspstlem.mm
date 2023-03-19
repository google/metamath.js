include "cv.mm"
include "cotp.mm"
include "wcel.mm"
include "co.mm"
include "wa.mm"
include "coprab.mm"
include "cop.mm"
include "wceq.mm"
include "wex.mm"
include "cab.mm"
include "df-oprab.mm"
include "df-ot.mm"
include "eqeq2i.mm"
include "biimpri.mm"
include "eleq1d.mm"
include "biimpar.mm"
include "adantrr.mm"
include "exlimiv.mm"
include "exlimivv.mm"
include "abssi.mm"
include "eqsstri.mm"

theorem mppspstlem
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
  assert |- { <. <. d , h >. , a >. | ( <. d , h , a >. e. P /\ a e. ( d C h ) ) } C_ P

  proof
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
    @2
    @0
    @1
    cC
    co
    wcel
    #
    wa
    #
    vd
    vh
    va
    coprab
    vx
    cv
    #
    @0
    @1
    cop
    @2
    cop
    #
    wceq
    #
    @6
    wa
    #
    va
    wex
    #
    vh
    wex
    vd
    wex
    #
    vx
    cab
    cP
    @6
    vd
    vh
    va
    vx
    df-oprab
    @12
    vx
    cP
    @11
    @7
    cP
    wcel
    #
    vd
    vh
    @10
    @13
    va
    @9
    @4
    @13
    @5
    @9
    @13
    @4
    @9
    @7
    @3
    cP
    @7
    @3
    wceq
    @9
    @3
    @8
    @7
    @0
    @1
    @2
    df-ot
    eqeq2i
    biimpri
    eleq1d
    biimpar
    adantrr
    exlimiv
    exlimivv
    abssi
    eqsstri
end
