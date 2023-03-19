include "cmre.mm"
include "cfv.mm"
include "wcel.mm"
include "cmrc.mm"
include "cpw.mm"
include "cv.mm"
include "wss.mm"
include "crab.mm"
include "cint.mm"
include "cmpt.mm"
include "cuni.mm"
include "crn.mm"
include "wceq.mm"
include "fvssunirn.mm"
include "sseli.mm"
include "cvv.mm"
include "unieq.mm"
include "pweqd.mm"
include "rabeq.mm"
include "inteqd.mm"
include "mpteq12dv.mm"
include "df-mrc.mm"
include "cxp.mm"
include "wf.mm"
include "mreunirn.mm"
include "mrcflem.mm"
include "sylbi.mm"
include "fssxp.mm"
include "syl.mm"
include "vuniex.mm"
include "pwex.mm"
include "vex.mm"
include "xpex.mm"
include "ssexg.mm"
include "sylancl.mm"
include "fvmpt3.mm"
include "mreuni.mm"
include "mpteq1d.mm"
include "eqtrd.mm"
include "syl5eq.mm"

theorem mrcfval
  let vx: setvar x
  let cC: class C
  let cF: class F
  let cX: class X
  let vs: setvar s
  let vc: setvar c
  let cU: class U
  let cV: class V
  assume mrcfval.f: |- F = ( mrCls ` C )

  disjoint F x
  disjoint F s
  disjoint s x
  disjoint C x
  disjoint C s
  disjoint X x
  disjoint X s
  disjoint F c
  disjoint c x
  disjoint c s
  disjoint C c
  disjoint X c
  disjoint U c
  disjoint U x
  disjoint U s
  disjoint V c
  disjoint V x
  disjoint V s
  assert |- ( C e. ( Moore ` X ) -> F = ( x e. ~P X |-> |^| { s e. C | x C_ s } ) )

  proof
    cC
    cX
    cmre
    cfv
    #
    wcel
    #
    cF
    cC
    cmrc
    cfv
    #
    vx
    cX
    cpw
    #
    vx
    cv
    vs
    cv
    wss
    #
    vs
    cC
    crab
    #
    cint
    #
    cmpt
    #
    mrcfval.f
    @1
    @2
    vx
    cC
    cuni
    #
    cpw
    #
    @6
    cmpt
    #
    @7
    @1
    cC
    cmre
    crn
    cuni
    #
    wcel
    @2
    @10
    wceq
    @0
    @11
    cC
    cmre
    cX
    fvssunirn
    sseli
    vc
    cC
    vx
    vc
    cv
    #
    cuni
    #
    cpw
    #
    @4
    vs
    @12
    crab
    #
    cint
    #
    cmpt
    #
    @10
    @11
    cmrc
    cvv
    @12
    cC
    wceq
    #
    vx
    @14
    @16
    @9
    @6
    @18
    @13
    @8
    @12
    cC
    unieq
    pweqd
    @18
    @15
    @5
    @4
    vs
    @12
    cC
    rabeq
    inteqd
    mpteq12dv
    vx
    vs
    vc
    df-mrc
    @12
    @11
    wcel
    #
    @17
    @14
    @12
    cxp
    #
    wss
    #
    @20
    cvv
    wcel
    @17
    cvv
    wcel
    @19
    @14
    @12
    @17
    wf
    #
    @21
    @19
    @12
    @13
    cmre
    cfv
    wcel
    @22
    @12
    mreunirn
    vx
    @12
    @13
    vs
    mrcflem
    sylbi
    @14
    @12
    @17
    fssxp
    syl
    @14
    @12
    @13
    vc
    vuniex
    pwex
    vc
    vex
    xpex
    @17
    @20
    cvv
    ssexg
    sylancl
    fvmpt3
    syl
    @1
    vx
    @9
    @3
    @6
    @1
    @8
    cX
    cC
    cX
    mreuni
    pweqd
    mpteq1d
    eqtrd
    syl5eq
end
