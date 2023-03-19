include "cmre.mm"
include "cfv.mm"
include "wcel.mm"
include "cv.mm"
include "csn.mm"
include "cdif.mm"
include "wn.mm"
include "wral.mm"
include "cuni.mm"
include "cpw.mm"
include "crab.mm"
include "cmri.mm"
include "crn.mm"
include "wceq.mm"
include "fvssunirn.mm"
include "sseli.mm"
include "cmrc.mm"
include "unieq.mm"
include "pweqd.mm"
include "fveq2.mm"
include "syl6eqr.mm"
include "fveq1d.mm"
include "eleq2d.mm"
include "notbid.mm"
include "ralbidv.mm"
include "rabeqbidv.mm"
include "df-mri.mm"
include "vuniex.mm"
include "pwex.mm"
include "rabex.mm"
include "fvmpt3i.mm"
include "syl.mm"
include "syl5eq.mm"
include "mreuni.mm"
include "rabeqdv.mm"
include "eqtrd.mm"

theorem mrisval
  let vx: setvar x
  let cA: class A
  let cI: class I
  let cN: class N
  let cX: class X
  let vs: setvar s
  let vc: setvar c
  assume mrisval.1: |- N = ( mrCls ` A )
  assume mrisval.2: |- I = ( mrInd ` A )

  disjoint A s
  disjoint A x
  disjoint s x
  disjoint X s
  disjoint A c
  disjoint c s
  disjoint c x
  disjoint N c
  assert |- ( A e. ( Moore ` X ) -> I = { s e. ~P X | A. x e. s -. x e. ( N ` ( s \ { x } ) ) } )

  proof
    cA
    cX
    cmre
    cfv
    #
    wcel
    #
    cI
    vx
    cv
    #
    vs
    cv
    #
    @2
    csn
    cdif
    #
    cN
    cfv
    #
    wcel
    #
    wn
    #
    vx
    @3
    wral
    #
    vs
    cA
    cuni
    #
    cpw
    #
    crab
    #
    @8
    vs
    cX
    cpw
    #
    crab
    @1
    cI
    cA
    cmri
    cfv
    #
    @11
    mrisval.2
    @1
    cA
    cmre
    crn
    cuni
    #
    wcel
    @13
    @11
    wceq
    @0
    @14
    cA
    cmre
    cX
    fvssunirn
    sseli
    vc
    cA
    @2
    @4
    vc
    cv
    #
    cmrc
    cfv
    #
    cfv
    #
    wcel
    #
    wn
    #
    vx
    @3
    wral
    #
    vs
    @15
    cuni
    #
    cpw
    #
    crab
    @11
    @14
    cmri
    @15
    cA
    wceq
    #
    @20
    @8
    vs
    @22
    @10
    @23
    @21
    @9
    @15
    cA
    unieq
    pweqd
    @23
    @19
    @7
    vx
    @3
    @23
    @18
    @6
    @23
    @17
    @5
    @2
    @23
    @4
    @16
    cN
    @23
    @16
    cA
    cmrc
    cfv
    cN
    @15
    cA
    cmrc
    fveq2
    mrisval.1
    syl6eqr
    fveq1d
    eleq2d
    notbid
    ralbidv
    rabeqbidv
    vx
    vs
    vc
    df-mri
    @20
    vs
    @22
    @21
    vc
    vuniex
    pwex
    rabex
    fvmpt3i
    syl
    syl5eq
    @1
    @8
    vs
    @10
    @12
    @1
    @9
    cX
    cA
    cX
    mreuni
    pweqd
    rabeqdv
    eqtrd
end
