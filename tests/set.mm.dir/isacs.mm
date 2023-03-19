include "cacs.mm"
include "cfv.mm"
include "wcel.mm"
include "cvv.mm"
include "cmre.mm"
include "cpw.mm"
include "cv.mm"
include "wf.mm"
include "cfn.mm"
include "cin.mm"
include "cima.mm"
include "cuni.mm"
include "wss.mm"
include "wb.mm"
include "wral.mm"
include "wa.mm"
include "wex.mm"
include "elfvex.mm"
include "adantr.mm"
include "wel.mm"
include "crab.mm"
include "wceq.mm"
include "fveq2.mm"
include "pweq.mm"
include "feq23d.mm"
include "raleqdv.mm"
include "anbi12d.mm"
include "exbidv.mm"
include "rabeqbidv.mm"
include "df-acs.mm"
include "fvex.mm"
include "rabex.mm"
include "fvmpt.mm"
include "eleq2d.mm"
include "eleq2.mm"
include "bibi1d.mm"
include "ralbidv.mm"
include "anbi2d.mm"
include "elrab.mm"
include "syl6bb.mm"
include "pm5.21nii.mm"

theorem isacs
  let cC: class C
  let vf: setvar f
  let cX: class X
  let vs: setvar s
  let vc: setvar c
  let vt: setvar t
  let vy: setvar y
  let cF: class F
  let vz: setvar z
  let cS: class S
  let vx: setvar x

  disjoint C f
  disjoint C s
  disjoint f s
  disjoint X f
  disjoint X s
  disjoint C c
  disjoint c f
  disjoint c s
  disjoint C t
  disjoint C y
  disjoint t y
  disjoint F f
  disjoint F s
  disjoint F t
  disjoint F y
  disjoint F z
  disjoint f t
  disjoint f y
  disjoint f z
  disjoint s t
  disjoint s y
  disjoint s z
  disjoint t z
  disjoint y z
  disjoint S s
  disjoint S y
  disjoint X c
  disjoint X x
  disjoint c x
  disjoint f x
  disjoint s x
  disjoint X t
  disjoint X y
  assert |- ( C e. ( ACS ` X ) <-> ( C e. ( Moore ` X ) /\ E. f ( f : ~P X --> ~P X /\ A. s e. ~P X ( s e. C <-> U. ( f " ( ~P s i^i Fin ) ) C_ s ) ) ) )

  proof
    cC
    cX
    cacs
    cfv
    #
    wcel
    #
    cX
    cvv
    wcel
    #
    cC
    cX
    cmre
    cfv
    #
    wcel
    #
    cX
    cpw
    #
    @5
    vf
    cv
    #
    wf
    #
    vs
    cv
    #
    cC
    wcel
    #
    @6
    @8
    cpw
    cfn
    cin
    cima
    cuni
    @8
    wss
    #
    wb
    #
    vs
    @5
    wral
    #
    wa
    #
    vf
    wex
    #
    wa
    #
    cC
    cX
    cacs
    elfvex
    @4
    @2
    @14
    cC
    cX
    cmre
    elfvex
    adantr
    @2
    @1
    cC
    @7
    vs
    vc
    wel
    #
    @10
    wb
    #
    vs
    @5
    wral
    #
    wa
    #
    vf
    wex
    #
    vc
    @3
    crab
    #
    wcel
    @15
    @2
    @0
    @21
    cC
    vx
    cX
    vx
    cv
    #
    cpw
    #
    @23
    @6
    wf
    #
    @17
    vs
    @23
    wral
    #
    wa
    #
    vf
    wex
    #
    vc
    @22
    cmre
    cfv
    #
    crab
    @21
    cvv
    cacs
    @22
    cX
    wceq
    #
    @27
    @20
    vc
    @28
    @3
    @22
    cX
    cmre
    fveq2
    @29
    @26
    @19
    vf
    @29
    @24
    @7
    @25
    @18
    @29
    @23
    @23
    @5
    @5
    @6
    @22
    cX
    pweq
    #
    @30
    feq23d
    @29
    @17
    vs
    @23
    @5
    @30
    raleqdv
    anbi12d
    exbidv
    rabeqbidv
    vx
    vf
    vs
    vc
    df-acs
    @20
    vc
    @3
    cX
    cmre
    fvex
    rabex
    fvmpt
    eleq2d
    @20
    @14
    vc
    cC
    @3
    vc
    cv
    #
    cC
    wceq
    #
    @19
    @13
    vf
    @32
    @18
    @12
    @7
    @32
    @17
    @11
    vs
    @5
    @32
    @16
    @9
    @10
    @31
    cC
    @8
    eleq2
    bibi1d
    ralbidv
    anbi2d
    exbidv
    elrab
    syl6bb
    pm5.21nii
end
