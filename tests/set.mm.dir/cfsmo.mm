include "cvv.mm"
include "cv.mm"
include "cdm.mm"
include "cfv.mm"
include "csuc.mm"
include "ciun.mm"
include "cun.mm"
include "cmpt.mm"
include "crecs.mm"
include "ccf.mm"
include "cres.mm"
include "wceq.mm"
include "dmeq.mm"
include "fveq2d.mm"
include "fveq2.mm"
include "suceq.mm"
include "syl.mm"
include "cbviunv.mm"
include "fveq1.mm"
include "iuneq12d.mm"
include "syl5eq.mm"
include "uneq12d.mm"
include "cbvmptv.mm"
include "eqid.mm"
include "cfsmolem.mm"

theorem cfsmo
  let vz: setvar z
  let vw: setvar w
  let cA: class A
  let vf: setvar f
  let vm: setvar m
  let vh: setvar h
  let vx: setvar x
  let vn: setvar n

  disjoint A f
  disjoint A w
  disjoint A z
  disjoint f w
  disjoint f z
  disjoint w z
  disjoint A m
  disjoint A h
  disjoint f m
  disjoint h m
  disjoint m w
  disjoint m z
  disjoint f h
  disjoint h w
  disjoint h z
  disjoint m x
  disjoint f x
  disjoint h x
  disjoint w x
  disjoint x z
  disjoint m n
  disjoint f n
  disjoint n x
  disjoint n w
  disjoint n z
  assert |- ( A e. On -> E. f ( f : ( cf ` A ) --> A /\ Smo f /\ A. z e. A E. w e. ( cf ` A ) z C_ ( f ` w ) ) )

  proof
    vz
    vw
    vm
    cA
    vf
    vh
    vx
    cvv
    vx
    cv
    #
    cdm
    #
    vh
    cv
    #
    cfv
    #
    vn
    @1
    vn
    cv
    #
    @0
    cfv
    #
    csuc
    #
    ciun
    #
    cun
    #
    cmpt
    #
    @9
    crecs
    cA
    ccf
    cfv
    cres
    #
    vx
    vz
    cvv
    @8
    vz
    cv
    #
    cdm
    #
    @2
    cfv
    #
    vm
    @12
    vm
    cv
    #
    @11
    cfv
    #
    csuc
    #
    ciun
    #
    cun
    @0
    @11
    wceq
    #
    @3
    @13
    @7
    @17
    @18
    @1
    @12
    @2
    @0
    @11
    dmeq
    #
    fveq2d
    @18
    @7
    vm
    @1
    @14
    @0
    cfv
    #
    csuc
    #
    ciun
    @17
    vn
    vm
    @1
    @6
    @21
    @4
    @14
    wceq
    @5
    @20
    wceq
    @6
    @21
    wceq
    @4
    @14
    @0
    fveq2
    @5
    @20
    suceq
    syl
    cbviunv
    @18
    vm
    @1
    @12
    @21
    @16
    @19
    @18
    @20
    @15
    wceq
    @21
    @16
    wceq
    @14
    @0
    @11
    fveq1
    @20
    @15
    suceq
    syl
    iuneq12d
    syl5eq
    uneq12d
    cbvmptv
    @10
    eqid
    cfsmolem
end
