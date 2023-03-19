include "cv.mm"
include "csuc.mm"
include "wf.mm"
include "c0.mm"
include "cfv.mm"
include "wceq.mm"
include "wcel.mm"
include "wral.mm"
include "w3a.mm"
include "com.mm"
include "wrex.mm"
include "cab.mm"
include "cdm.mm"
include "cres.mm"
include "wa.mm"
include "crab.mm"
include "cmpt.mm"
include "feq1.mm"
include "fveq1.mm"
include "eqeq1d.mm"
include "fveq2d.mm"
include "eleq12d.mm"
include "ralbidv.mm"
include "suceq.mm"
include "fveq2.mm"
include "cbvralv.mm"
include "syl6bb.mm"
include "3anbi123d.mm"
include "rexbidv.mm"
include "cbvabv.mm"
include "eqid.mm"
include "axdc3lem4.mm"

theorem axdc3
  let cA: class A
  let cC: class C
  let vg: setvar g
  let vk: setvar k
  let cF: class F
  let vn: setvar n
  let vs: setvar s
  let vt: setvar t
  let vx: setvar x
  let vy: setvar y
  let vj: setvar j
  assume axdc3.1: |- A e. _V

  disjoint A g
  disjoint A k
  disjoint g k
  disjoint C g
  disjoint C k
  disjoint F g
  disjoint F k
  disjoint A n
  disjoint A s
  disjoint A t
  disjoint A x
  disjoint k n
  disjoint k s
  disjoint k t
  disjoint k x
  disjoint n s
  disjoint n t
  disjoint n x
  disjoint s t
  disjoint s x
  disjoint t x
  disjoint A y
  disjoint k y
  disjoint n y
  disjoint t y
  disjoint x y
  disjoint C n
  disjoint C s
  disjoint C t
  disjoint C x
  disjoint C y
  disjoint F j
  disjoint F n
  disjoint F s
  disjoint F t
  disjoint F x
  disjoint j k
  disjoint j n
  disjoint j s
  disjoint j t
  disjoint j x
  disjoint F y
  disjoint j y
  assert |- ( ( C e. A /\ F : A --> ( ~P A \ { (/) } ) ) -> E. g ( g : _om --> A /\ ( g ` (/) ) = C /\ A. k e. _om ( g ` suc k ) e. ( F ` ( g ` k ) ) ) )

  proof
    vx
    vy
    cA
    cC
    vn
    cv
    #
    csuc
    #
    cA
    vt
    cv
    #
    wf
    #
    c0
    @2
    cfv
    #
    cC
    wceq
    #
    vj
    cv
    #
    csuc
    #
    @2
    cfv
    #
    @6
    @2
    cfv
    #
    cF
    cfv
    #
    wcel
    #
    vj
    @0
    wral
    #
    w3a
    #
    vn
    com
    wrex
    #
    vt
    cab
    #
    vg
    vk
    vn
    cF
    vx
    @15
    vy
    cv
    #
    cdm
    vx
    cv
    #
    cdm
    #
    csuc
    wceq
    @16
    @18
    cres
    @17
    wceq
    wa
    vy
    @15
    crab
    cmpt
    #
    vs
    axdc3.1
    @14
    @1
    cA
    vs
    cv
    #
    wf
    #
    c0
    @20
    cfv
    #
    cC
    wceq
    #
    vk
    cv
    #
    csuc
    #
    @20
    cfv
    #
    @24
    @20
    cfv
    #
    cF
    cfv
    #
    wcel
    #
    vk
    @0
    wral
    #
    w3a
    #
    vn
    com
    wrex
    vt
    vs
    @2
    @20
    wceq
    #
    @13
    @31
    vn
    com
    @32
    @3
    @21
    @5
    @23
    @12
    @30
    @1
    cA
    @2
    @20
    feq1
    @32
    @4
    @22
    cC
    c0
    @2
    @20
    fveq1
    eqeq1d
    @32
    @12
    @7
    @20
    cfv
    #
    @6
    @20
    cfv
    #
    cF
    cfv
    #
    wcel
    #
    vj
    @0
    wral
    @30
    @32
    @11
    @36
    vj
    @0
    @32
    @8
    @33
    @10
    @35
    @7
    @2
    @20
    fveq1
    @32
    @9
    @34
    cF
    @6
    @2
    @20
    fveq1
    fveq2d
    eleq12d
    ralbidv
    @36
    @29
    vj
    vk
    @0
    @6
    @24
    wceq
    #
    @33
    @26
    @35
    @28
    @37
    @7
    @25
    @20
    @6
    @24
    suceq
    fveq2d
    @37
    @34
    @27
    cF
    @6
    @24
    @20
    fveq2
    fveq2d
    eleq12d
    cbvralv
    syl6bb
    3anbi123d
    rexbidv
    cbvabv
    @19
    eqid
    axdc3lem4
end
