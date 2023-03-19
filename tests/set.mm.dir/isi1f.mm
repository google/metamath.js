include "cr.mm"
include "cv.mm"
include "wf.mm"
include "crn.mm"
include "cfn.mm"
include "wcel.mm"
include "ccnv.mm"
include "cc0.mm"
include "csn.mm"
include "cdif.mm"
include "cima.mm"
include "cvol.mm"
include "cfv.mm"
include "w3a.mm"
include "cmbf.mm"
include "citg1.mm"
include "cdm.mm"
include "wceq.mm"
include "feq1.mm"
include "rneq.mm"
include "eleq1d.mm"
include "cnveq.mm"
include "imaeq1d.mm"
include "fveq2d.mm"
include "3anbi123d.mm"
include "crab.mm"
include "cmul.mm"
include "co.mm"
include "csu.mm"
include "sumex.mm"
include "df-itg1.mm"
include "dmmpti.mm"
include "elrab2.mm"

theorem isi1f
  let cF: class F
  let vf: setvar f
  let vg: setvar g
  let vx: setvar x
  let vy: setvar y
  let cA: class A


  assert |- ( F e. dom S.1 <-> ( F e. MblFn /\ ( F : RR --> RR /\ ran F e. Fin /\ ( vol ` ( `' F " ( RR \ { 0 } ) ) ) e. RR ) ) )

  proof
    cr
    cr
    vg
    cv
    #
    wf
    #
    @0
    crn
    #
    cfn
    wcel
    #
    @0
    ccnv
    #
    cr
    cc0
    csn
    #
    cdif
    #
    cima
    #
    cvol
    cfv
    #
    cr
    wcel
    #
    w3a
    #
    cr
    cr
    cF
    wf
    #
    cF
    crn
    #
    cfn
    wcel
    #
    cF
    ccnv
    #
    @6
    cima
    #
    cvol
    cfv
    #
    cr
    wcel
    #
    w3a
    vg
    cF
    cmbf
    citg1
    cdm
    @0
    cF
    wceq
    #
    @1
    @11
    @3
    @13
    @9
    @17
    cr
    cr
    @0
    cF
    feq1
    @18
    @2
    @12
    cfn
    @0
    cF
    rneq
    eleq1d
    @18
    @8
    @16
    cr
    @18
    @7
    @15
    cvol
    @18
    @4
    @14
    @6
    @0
    cF
    cnveq
    imaeq1d
    fveq2d
    eleq1d
    3anbi123d
    vf
    @10
    vg
    cmbf
    crab
    vf
    cv
    #
    crn
    @5
    cdif
    #
    vx
    cv
    #
    @19
    ccnv
    @21
    csn
    cima
    cvol
    cfv
    cmul
    co
    #
    vx
    csu
    citg1
    @20
    @22
    vx
    sumex
    vx
    vf
    vg
    df-itg1
    dmmpti
    elrab2
end
