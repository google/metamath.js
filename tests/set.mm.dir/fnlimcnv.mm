include "cv.mm"
include "cfv.mm"
include "cmpt.mm"
include "cli.mm"
include "cdm.mm"
include "wcel.mm"
include "wbr.mm"
include "cuz.mm"
include "ciin.mm"
include "ciun.mm"
include "wa.mm"
include "wceq.mm"
include "fveq2.mm"
include "mpteq2dv.mm"
include "eleq1d.mm"
include "crab.mm"
include "nfcv.mm"
include "nffv.mm"
include "nfdm.mm"
include "nfiin.mm"
include "nfiun.mm"
include "nfv.mm"
include "nfmpt.mm"
include "nfel.mm"
include "cbvrab.mm"
include "eqtri.mm"
include "elrab2.mm"
include "sylib.mm"
include "simprd.mm"
include "climdm.mm"
include "nfrab1.mm"
include "nfcxfr.mm"
include "fnlimfv.mm"
include "eqcomd.mm"
include "breqtrd.mm"

theorem fnlimcnv
  let wph: wff ph
  let vx: setvar x
  let cD: class D
  let vm: setvar m
  let vn: setvar n
  let cF: class F
  let cG: class G
  let cX: class X
  let cZ: class Z
  let vy: setvar y
  assume fnlimcnv.1: |- F/_ x F
  assume fnlimcnv.2: |- D = { x e. U_ n e. Z |^|_ m e. ( ZZ>= ` n ) dom ( F ` m ) | ( m e. Z |-> ( ( F ` m ) ` x ) ) e. dom ~~> }
  assume fnlimcnv.3: |- G = ( x e. D |-> ( ~~> ` ( m e. Z |-> ( ( F ` m ) ` x ) ) ) )
  assume fnlimcnv.4: |- ( ph -> X e. D )

  disjoint X m
  disjoint Z x
  disjoint m x
  disjoint n x
  disjoint F y
  disjoint X y
  disjoint m y
  disjoint Z y
  disjoint x y
  disjoint n y
  assert |- ( ph -> ( m e. Z |-> ( ( F ` m ) ` X ) ) ~~> ( G ` X ) )

  proof
    wph
    vm
    cZ
    cX
    vm
    cv
    #
    cF
    cfv
    #
    cfv
    #
    cmpt
    #
    @3
    cli
    cfv
    #
    cX
    cG
    cfv
    #
    cli
    wph
    @3
    cli
    cdm
    #
    wcel
    #
    @3
    @4
    cli
    wbr
    wph
    cX
    vn
    cZ
    vm
    vn
    cv
    cuz
    cfv
    #
    @1
    cdm
    #
    ciin
    #
    ciun
    #
    wcel
    #
    @7
    wph
    cX
    cD
    wcel
    @12
    @7
    wa
    fnlimcnv.4
    vm
    cZ
    vy
    cv
    #
    @1
    cfv
    #
    cmpt
    #
    @6
    wcel
    #
    @7
    vy
    cX
    @11
    cD
    @13
    cX
    wceq
    #
    @15
    @3
    @6
    @17
    vm
    cZ
    @14
    @2
    @13
    cX
    @1
    fveq2
    mpteq2dv
    eleq1d
    cD
    vm
    cZ
    vx
    cv
    #
    @1
    cfv
    #
    cmpt
    #
    @6
    wcel
    #
    vx
    @11
    crab
    #
    @16
    vy
    @11
    crab
    fnlimcnv.2
    @21
    @16
    vx
    vy
    @11
    vn
    vx
    cZ
    @10
    vx
    cZ
    nfcv
    #
    vm
    vx
    @8
    @9
    vx
    @8
    nfcv
    vx
    @1
    vx
    @0
    cF
    fnlimcnv.1
    vx
    @0
    nfcv
    nffv
    #
    nfdm
    nfiin
    nfiun
    vy
    @11
    nfcv
    @21
    vy
    nfv
    vx
    @15
    @6
    vx
    vm
    cZ
    @14
    @23
    vx
    @13
    @1
    @24
    vx
    @13
    nfcv
    nffv
    nfmpt
    vx
    @6
    nfcv
    nfel
    @18
    @13
    wceq
    #
    @20
    @15
    @6
    @25
    vm
    cZ
    @19
    @14
    @18
    @13
    @1
    fveq2
    mpteq2dv
    eleq1d
    cbvrab
    eqtri
    elrab2
    sylib
    simprd
    @3
    climdm
    sylib
    wph
    @5
    @4
    wph
    vx
    cD
    vm
    cF
    cG
    cX
    cZ
    vx
    cD
    @22
    fnlimcnv.2
    @21
    vx
    @11
    nfrab1
    nfcxfr
    fnlimcnv.1
    fnlimcnv.3
    fnlimcnv.4
    fnlimfv
    eqcomd
    breqtrd
end
