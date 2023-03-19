include "cfv.mm"
include "cv.mm"
include "cmpt.mm"
include "cli.mm"
include "cr.mm"
include "wcel.mm"
include "cvv.mm"
include "wceq.mm"
include "fvexd.mm"
include "nfcv.mm"
include "wi.mm"
include "fveq2.mm"
include "mpteq2dv.mm"
include "eqcom.mm"
include "imbi1i.mm"
include "imbi2i.mm"
include "bitri.mm"
include "mpbi.mm"
include "fveq2d.mm"
include "cdm.mm"
include "cuz.mm"
include "ciin.mm"
include "ciun.mm"
include "crab.mm"
include "nfrab1.mm"
include "nfcxfr.mm"
include "nffv.mm"
include "nfmpt.mm"
include "cbvmptf.mm"
include "eqtri.mm"
include "fvmptf.mm"
include "syl2anc.mm"
include "fnlimfvre.mm"
include "eqeltrd.mm"

theorem fnlimfvre2
  let wph: wff ph
  let vx: setvar x
  let cD: class D
  let vm: setvar m
  let vn: setvar n
  let cF: class F
  let cG: class G
  let cM: class M
  let cX: class X
  let cZ: class Z
  let vz: setvar z
  assume fnlimfvre2.p: |- F/ m ph
  assume fnlimfvre2.m: |- F/_ m F
  assume fnlimfvre2.n: |- F/_ x F
  assume fnlimfvre2.z: |- Z = ( ZZ>= ` M )
  assume fnlimfvre2.f: |- ( ( ph /\ m e. Z ) -> ( F ` m ) : dom ( F ` m ) --> RR )
  assume fnlimfvre2.d: |- D = { x e. U_ n e. Z |^|_ m e. ( ZZ>= ` n ) dom ( F ` m ) | ( m e. Z |-> ( ( F ` m ) ` x ) ) e. dom ~~> }
  assume fnlimfvre2.g: |- G = ( x e. D |-> ( ~~> ` ( m e. Z |-> ( ( F ` m ) ` x ) ) ) )
  assume fnlimfvre2.x: |- ( ph -> X e. D )

  disjoint F n
  disjoint X m
  disjoint X n
  disjoint X x
  disjoint m n
  disjoint m x
  disjoint n x
  disjoint Z m
  disjoint Z n
  disjoint Z x
  disjoint n ph
  disjoint D z
  disjoint F z
  disjoint n z
  disjoint X z
  disjoint m z
  disjoint x z
  disjoint Z z
  assert |- ( ph -> ( G ` X ) e. RR )

  proof
    wph
    cX
    cG
    cfv
    #
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
    cli
    cfv
    #
    cr
    wph
    cX
    cD
    wcel
    @5
    cvv
    wcel
    @0
    @5
    wceq
    fnlimfvre2.x
    wph
    @4
    cli
    fvexd
    vz
    cX
    vm
    cZ
    vz
    cv
    #
    @2
    cfv
    #
    cmpt
    #
    cli
    cfv
    #
    @5
    cD
    cG
    cvv
    vz
    cX
    nfcv
    vz
    @5
    nfcv
    @6
    cX
    wceq
    #
    @8
    @4
    cli
    cX
    @6
    wceq
    #
    @4
    @8
    wceq
    #
    wi
    #
    @10
    @8
    @4
    wceq
    #
    wi
    #
    @11
    vm
    cZ
    @3
    @7
    cX
    @6
    @2
    fveq2
    mpteq2dv
    @13
    @10
    @12
    wi
    @15
    @11
    @10
    @12
    cX
    @6
    eqcom
    imbi1i
    @12
    @14
    @10
    @4
    @8
    eqcom
    imbi2i
    bitri
    mpbi
    fveq2d
    cG
    vx
    cD
    vm
    cZ
    vx
    cv
    #
    @2
    cfv
    #
    cmpt
    #
    cli
    cfv
    #
    cmpt
    vz
    cD
    @9
    cmpt
    fnlimfvre2.g
    vx
    vz
    cD
    @19
    @9
    vx
    cD
    @18
    cli
    cdm
    wcel
    #
    vx
    vn
    cZ
    vm
    vn
    cv
    cuz
    cfv
    @2
    cdm
    ciin
    ciun
    #
    crab
    fnlimfvre2.d
    @20
    vx
    @21
    nfrab1
    nfcxfr
    vz
    cD
    nfcv
    vz
    @19
    nfcv
    vx
    @8
    cli
    vx
    cli
    nfcv
    vx
    vm
    cZ
    @7
    vx
    cZ
    nfcv
    vx
    @6
    @2
    vx
    @1
    cF
    fnlimfvre2.n
    vx
    @1
    nfcv
    nffv
    vx
    @6
    nfcv
    nffv
    nfmpt
    nffv
    @16
    @6
    wceq
    #
    @18
    @8
    cli
    @22
    vm
    cZ
    @17
    @7
    @16
    @6
    @2
    fveq2
    mpteq2dv
    fveq2d
    cbvmptf
    eqtri
    fvmptf
    syl2anc
    wph
    vx
    cD
    vm
    vn
    cF
    cM
    cX
    cZ
    fnlimfvre2.p
    fnlimfvre2.m
    fnlimfvre2.n
    fnlimfvre2.z
    fnlimfvre2.f
    fnlimfvre2.d
    fnlimfvre2.x
    fnlimfvre
    eqeltrd
end
