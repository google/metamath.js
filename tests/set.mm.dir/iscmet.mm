include "cms.mm"
include "cfv.mm"
include "wcel.mm"
include "cvv.mm"
include "cme.mm"
include "cv.mm"
include "cflim.mm"
include "co.mm"
include "c0.mm"
include "wne.mm"
include "ccfil.mm"
include "wral.mm"
include "wa.mm"
include "elfvex.mm"
include "adantr.mm"
include "cmopn.mm"
include "crab.mm"
include "wceq.mm"
include "fveq2.mm"
include "rabeq.mm"
include "syl.mm"
include "df-cmet.mm"
include "fvex.mm"
include "rabex.mm"
include "fvmpt.mm"
include "eleq2d.mm"
include "syl6eqr.mm"
include "oveq1d.mm"
include "neeq1d.mm"
include "raleqbidv.mm"
include "elrab.mm"
include "syl6bb.mm"
include "pm5.21nii.mm"

theorem iscmet
  let cD: class D
  let vf: setvar f
  let cJ: class J
  let cX: class X
  let vd: setvar d
  let cF: class F
  let vx: setvar x
  assume iscmet.1: |- J = ( MetOpen ` D )

  disjoint D f
  disjoint J f
  disjoint X f
  disjoint d f
  disjoint D d
  disjoint F f
  disjoint J d
  disjoint d x
  disjoint X d
  disjoint f x
  disjoint X x
  assert |- ( D e. ( CMet ` X ) <-> ( D e. ( Met ` X ) /\ A. f e. ( CauFil ` D ) ( J fLim f ) =/= (/) ) )

  proof
    cD
    cX
    cms
    cfv
    #
    wcel
    #
    cX
    cvv
    wcel
    #
    cD
    cX
    cme
    cfv
    #
    wcel
    #
    cJ
    vf
    cv
    #
    cflim
    co
    #
    c0
    wne
    #
    vf
    cD
    ccfil
    cfv
    #
    wral
    #
    wa
    #
    cD
    cX
    cms
    elfvex
    @4
    @2
    @9
    cD
    cX
    cme
    elfvex
    adantr
    @2
    @1
    cD
    vd
    cv
    #
    cmopn
    cfv
    #
    @5
    cflim
    co
    #
    c0
    wne
    #
    vf
    @11
    ccfil
    cfv
    #
    wral
    #
    vd
    @3
    crab
    #
    wcel
    @10
    @2
    @0
    @17
    cD
    vx
    cX
    @16
    vd
    vx
    cv
    #
    cme
    cfv
    #
    crab
    #
    @17
    cvv
    cms
    @18
    cX
    wceq
    @19
    @3
    wceq
    @20
    @17
    wceq
    @18
    cX
    cme
    fveq2
    @16
    vd
    @19
    @3
    rabeq
    syl
    vx
    vf
    vd
    df-cmet
    @16
    vd
    @3
    cX
    cme
    fvex
    rabex
    fvmpt
    eleq2d
    @16
    @9
    vd
    cD
    @3
    @11
    cD
    wceq
    #
    @14
    @7
    vf
    @15
    @8
    @11
    cD
    ccfil
    fveq2
    @21
    @13
    @6
    c0
    @21
    @12
    cJ
    @5
    cflim
    @21
    @12
    cD
    cmopn
    cfv
    cJ
    @11
    cD
    cmopn
    fveq2
    iscmet.1
    syl6eqr
    oveq1d
    neeq1d
    raleqbidv
    elrab
    syl6bb
    pm5.21nii
end
