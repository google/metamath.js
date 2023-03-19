include "citg1.mm"
include "cfv.mm"
include "crn.mm"
include "cc0.mm"
include "csn.mm"
include "cdif.mm"
include "cv.mm"
include "ccnv.mm"
include "cima.mm"
include "cvol.mm"
include "cmul.mm"
include "co.mm"
include "csu.mm"
include "wceq.mm"
include "cr.mm"
include "wf.mm"
include "cfn.mm"
include "wcel.mm"
include "w3a.mm"
include "cmbf.mm"
include "crab.mm"
include "cdm.mm"
include "rneq.mm"
include "difeq1d.mm"
include "cnveq.mm"
include "imaeq1d.mm"
include "fveq2d.mm"
include "oveq2d.mm"
include "adantr.mm"
include "sumeq12dv.mm"
include "df-itg1.mm"
include "sumex.mm"
include "fvmpt.mm"
include "dmmpti.mm"
include "eleq2s.mm"

theorem itg1val
  let vx: setvar x
  let cF: class F
  let vf: setvar f
  let vg: setvar g
  let vy: setvar y
  let cA: class A

  disjoint F x
  disjoint f g
  disjoint f x
  disjoint f y
  disjoint F f
  disjoint g x
  disjoint g y
  disjoint F g
  disjoint x y
  disjoint F y
  disjoint A x
  disjoint A y
  assert |- ( F e. dom S.1 -> ( S.1 ` F ) = sum_ x e. ( ran F \ { 0 } ) ( x x. ( vol ` ( `' F " { x } ) ) ) )

  proof
    cF
    citg1
    cfv
    cF
    crn
    #
    cc0
    csn
    #
    cdif
    #
    vx
    cv
    #
    cF
    ccnv
    #
    @3
    csn
    #
    cima
    #
    cvol
    cfv
    #
    cmul
    co
    #
    vx
    csu
    #
    wceq
    cF
    cr
    cr
    vg
    cv
    #
    wf
    @10
    crn
    cfn
    wcel
    @10
    ccnv
    cr
    @1
    cdif
    cima
    cvol
    cfv
    cr
    wcel
    w3a
    vg
    cmbf
    crab
    #
    citg1
    cdm
    vf
    cF
    vf
    cv
    #
    crn
    #
    @1
    cdif
    #
    @3
    @12
    ccnv
    #
    @5
    cima
    #
    cvol
    cfv
    #
    cmul
    co
    #
    vx
    csu
    #
    @9
    @11
    citg1
    @12
    cF
    wceq
    #
    @14
    @2
    @18
    @8
    vx
    @20
    @13
    @0
    @1
    @12
    cF
    rneq
    difeq1d
    @20
    @18
    @8
    wceq
    @3
    @14
    wcel
    @20
    @17
    @7
    @3
    cmul
    @20
    @16
    @6
    cvol
    @20
    @15
    @4
    @5
    @12
    cF
    cnveq
    imaeq1d
    fveq2d
    oveq2d
    adantr
    sumeq12dv
    vx
    vf
    vg
    df-itg1
    #
    @2
    @8
    vx
    sumex
    fvmpt
    vf
    @11
    @19
    citg1
    @14
    @18
    vx
    sumex
    @21
    dmmpti
    eleq2s
end
