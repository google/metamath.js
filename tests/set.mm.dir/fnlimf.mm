include "cv.mm"
include "cfv.mm"
include "cmpt.mm"
include "cli.mm"
include "cr.mm"
include "wcel.mm"
include "wa.mm"
include "nfv.mm"
include "nfan.mm"
include "cdm.mm"
include "wf.mm"
include "adantlr.mm"
include "simpr.mm"
include "fnlimfvre.mm"
include "cuz.mm"
include "ciin.mm"
include "ciun.mm"
include "crab.mm"
include "nfrab1.mm"
include "nfcxfr.mm"
include "nfcv.mm"
include "nffv.mm"
include "nfmpt.mm"
include "wceq.mm"
include "fveq2.mm"
include "mpteq2dv.mm"
include "fveq2d.mm"
include "cbvmptf.mm"
include "eqtri.mm"
include "fmptd.mm"

theorem fnlimf
  let wph: wff ph
  let vx: setvar x
  let cD: class D
  let vm: setvar m
  let vn: setvar n
  let cF: class F
  let cG: class G
  let cM: class M
  let cZ: class Z
  let vz: setvar z
  assume fnlimf.p: |- F/ m ph
  assume fnlimf.m: |- F/_ m F
  assume fnlimf.n: |- F/_ x F
  assume fnlimf.z: |- Z = ( ZZ>= ` M )
  assume fnlimf.f: |- ( ( ph /\ m e. Z ) -> ( F ` m ) : dom ( F ` m ) --> RR )
  assume fnlimf.d: |- D = { x e. U_ n e. Z |^|_ m e. ( ZZ>= ` n ) dom ( F ` m ) | ( m e. Z |-> ( ( F ` m ) ` x ) ) e. dom ~~> }
  assume fnlimf.g: |- G = ( x e. D |-> ( ~~> ` ( m e. Z |-> ( ( F ` m ) ` x ) ) ) )

  disjoint D m
  disjoint D n
  disjoint m n
  disjoint F n
  disjoint Z m
  disjoint Z n
  disjoint Z x
  disjoint m x
  disjoint n x
  disjoint n ph
  disjoint D z
  disjoint m z
  disjoint n z
  disjoint F z
  disjoint Z z
  disjoint x z
  disjoint ph z
  assert |- ( ph -> G : D --> RR )

  proof
    wph
    vz
    cD
    vm
    cZ
    vz
    cv
    #
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
    cG
    wph
    @0
    cD
    wcel
    #
    wa
    vx
    cD
    vm
    vn
    cF
    cM
    @0
    cZ
    wph
    @6
    vm
    fnlimf.p
    @6
    vm
    nfv
    nfan
    fnlimf.m
    fnlimf.n
    fnlimf.z
    wph
    @1
    cZ
    wcel
    @2
    cdm
    #
    cr
    @2
    wf
    @6
    fnlimf.f
    adantlr
    fnlimf.d
    wph
    @6
    simpr
    fnlimfvre
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
    @5
    cmpt
    fnlimf.g
    vx
    vz
    cD
    @11
    @5
    vx
    cD
    @10
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
    @7
    ciin
    ciun
    #
    crab
    fnlimf.d
    @12
    vx
    @13
    nfrab1
    nfcxfr
    vz
    cD
    nfcv
    vz
    @11
    nfcv
    vx
    @4
    cli
    vx
    cli
    nfcv
    vx
    vm
    cZ
    @3
    vx
    cZ
    nfcv
    vx
    @0
    @2
    vx
    @1
    cF
    fnlimf.n
    vx
    @1
    nfcv
    nffv
    vx
    @0
    nfcv
    nffv
    nfmpt
    nffv
    @8
    @0
    wceq
    #
    @10
    @4
    cli
    @14
    vm
    cZ
    @9
    @3
    @8
    @0
    @2
    fveq2
    mpteq2dv
    fveq2d
    cbvmptf
    eqtri
    fmptd
end
