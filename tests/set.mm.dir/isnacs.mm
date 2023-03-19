include "cnacs.mm"
include "cfv.mm"
include "wcel.mm"
include "cvv.mm"
include "cacs.mm"
include "cv.mm"
include "wceq.mm"
include "cpw.mm"
include "cfn.mm"
include "cin.mm"
include "wrex.mm"
include "wral.mm"
include "wa.mm"
include "elfvex.mm"
include "adantr.mm"
include "cmrc.mm"
include "crab.mm"
include "fveq2.mm"
include "pweq.mm"
include "ineq1d.mm"
include "rexeqdv.mm"
include "ralbidv.mm"
include "rabeqbidv.mm"
include "df-nacs.mm"
include "fvex.mm"
include "rabex.mm"
include "fvmpt.mm"
include "eleq2d.mm"
include "syl6eqr.mm"
include "fveq1d.mm"
include "eqeq2d.mm"
include "rexbidv.mm"
include "raleqbi1dv.mm"
include "elrab.mm"
include "syl6bb.mm"
include "pm5.21nii.mm"

theorem isnacs
  let cC: class C
  let vg: setvar g
  let cF: class F
  let cX: class X
  let vs: setvar s
  let vc: setvar c
  let cS: class S
  let vx: setvar x
  assume isnacs.f: |- F = ( mrCls ` C )

  disjoint C g
  disjoint C s
  disjoint g s
  disjoint F g
  disjoint F s
  disjoint X g
  disjoint X s
  disjoint C c
  disjoint c g
  disjoint c s
  disjoint F c
  disjoint S g
  disjoint S s
  disjoint X c
  disjoint X x
  disjoint c x
  disjoint g x
  disjoint s x
  assert |- ( C e. ( NoeACS ` X ) <-> ( C e. ( ACS ` X ) /\ A. s e. C E. g e. ( ~P X i^i Fin ) s = ( F ` g ) ) )

  proof
    cC
    cX
    cnacs
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
    cacs
    cfv
    #
    wcel
    #
    vs
    cv
    #
    vg
    cv
    #
    cF
    cfv
    #
    wceq
    #
    vg
    cX
    cpw
    #
    cfn
    cin
    #
    wrex
    #
    vs
    cC
    wral
    #
    wa
    #
    cC
    cX
    cnacs
    elfvex
    @4
    @2
    @12
    cC
    cX
    cacs
    elfvex
    adantr
    @2
    @1
    cC
    @5
    @6
    vc
    cv
    #
    cmrc
    cfv
    #
    cfv
    #
    wceq
    #
    vg
    @10
    wrex
    #
    vs
    @14
    wral
    #
    vc
    @3
    crab
    #
    wcel
    @13
    @2
    @0
    @20
    cC
    vx
    cX
    @17
    vg
    vx
    cv
    #
    cpw
    #
    cfn
    cin
    #
    wrex
    #
    vs
    @14
    wral
    #
    vc
    @21
    cacs
    cfv
    #
    crab
    @20
    cvv
    cnacs
    @21
    cX
    wceq
    #
    @25
    @19
    vc
    @26
    @3
    @21
    cX
    cacs
    fveq2
    @27
    @24
    @18
    vs
    @14
    @27
    @17
    vg
    @23
    @10
    @27
    @22
    @9
    cfn
    @21
    cX
    pweq
    ineq1d
    rexeqdv
    ralbidv
    rabeqbidv
    vx
    vg
    vs
    vc
    df-nacs
    @19
    vc
    @3
    cX
    cacs
    fvex
    rabex
    fvmpt
    eleq2d
    @19
    @12
    vc
    cC
    @3
    @18
    @11
    vs
    @14
    cC
    @14
    cC
    wceq
    #
    @17
    @8
    vg
    @10
    @28
    @16
    @7
    @5
    @28
    @6
    @15
    cF
    @28
    @15
    cC
    cmrc
    cfv
    cF
    @14
    cC
    cmrc
    fveq2
    isnacs.f
    syl6eqr
    fveq1d
    eqeq2d
    rexbidv
    raleqbi1dv
    elrab
    syl6bb
    pm5.21nii
end
