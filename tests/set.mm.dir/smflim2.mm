include "nfcv.mm"
include "cv.mm"
include "cfv.mm"
include "cmpt.mm"
include "cli.mm"
include "cdm.mm"
include "wcel.mm"
include "cuz.mm"
include "ciin.mm"
include "ciun.mm"
include "crab.mm"
include "nffv.mm"
include "nfdm.mm"
include "nfiin.mm"
include "nfiun.mm"
include "nfv.mm"
include "wceq.mm"
include "fveq2.mm"
include "fveq1d.mm"
include "cbvmpt.mm"
include "nfmpt.mm"
include "nfcxfr.mm"
include "nfel.mm"
include "mpteq2dv.mm"
include "eleq1d.mm"
include "cbvrab.mm"
include "iineq1d.mm"
include "dmeqd.mm"
include "cbviin.mm"
include "a1i.mm"
include "eqtrd.mm"
include "cbviunv.mm"
include "eleq2i.mm"
include "eleq1i.mm"
include "anbi12i.mm"
include "rabbia2.mm"
include "3eqtri.mm"
include "nfrab1.mm"
include "fveq2d.mm"
include "cbvmptf.mm"
include "eqtri.mm"
include "smflim.mm"

theorem smflim2
  let wph: wff ph
  let vx: setvar x
  let cD: class D
  let cS: class S
  let vm: setvar m
  let vn: setvar n
  let cF: class F
  let cG: class G
  let cM: class M
  let cZ: class Z
  let vy: setvar y
  let vj: setvar j
  let vk: setvar k
  assume smflim2.n: |- F/_ m F
  assume smflim2.x: |- F/_ x F
  assume smflim2.m: |- ( ph -> M e. ZZ )
  assume smflim2.z: |- Z = ( ZZ>= ` M )
  assume smflim2.s: |- ( ph -> S e. SAlg )
  assume smflim2.f: |- ( ph -> F : Z --> ( SMblFn ` S ) )
  assume smflim2.d: |- D = { x e. U_ n e. Z |^|_ m e. ( ZZ>= ` n ) dom ( F ` m ) | ( m e. Z |-> ( ( F ` m ) ` x ) ) e. dom ~~> }
  assume smflim2.g: |- G = ( x e. D |-> ( ~~> ` ( m e. Z |-> ( ( F ` m ) ` x ) ) ) )

  disjoint F n
  disjoint Z m
  disjoint Z n
  disjoint m n
  disjoint Z x
  disjoint m x
  disjoint n x
  disjoint D y
  disjoint F j
  disjoint F k
  disjoint F y
  disjoint j k
  disjoint j n
  disjoint j y
  disjoint k n
  disjoint k y
  disjoint n y
  disjoint S j
  disjoint S k
  disjoint Z j
  disjoint Z k
  disjoint Z y
  disjoint j m
  disjoint k m
  disjoint m y
  disjoint j x
  disjoint x y
  disjoint j ph
  disjoint k ph
  disjoint k x
  assert |- ( ph -> G e. ( SMblFn ` S ) )

  proof
    wph
    vy
    cD
    cS
    vj
    vk
    cF
    cG
    cM
    cZ
    vj
    cF
    nfcv
    vy
    cF
    nfcv
    smflim2.m
    smflim2.z
    smflim2.s
    smflim2.f
    cD
    vm
    cZ
    vx
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
    cdm
    #
    wcel
    #
    vx
    vn
    cZ
    vm
    vn
    cv
    #
    cuz
    cfv
    #
    @2
    cdm
    #
    ciin
    #
    ciun
    #
    crab
    #
    vm
    cZ
    vy
    cv
    #
    @2
    cfv
    #
    cmpt
    #
    @5
    wcel
    #
    vy
    @11
    crab
    vj
    cZ
    @13
    vj
    cv
    #
    cF
    cfv
    #
    cfv
    #
    cmpt
    #
    @5
    wcel
    #
    vy
    vk
    cZ
    vj
    vk
    cv
    #
    cuz
    cfv
    #
    @18
    cdm
    #
    ciin
    #
    ciun
    #
    crab
    smflim2.d
    @6
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
    @2
    vx
    @1
    cF
    smflim2.x
    vx
    @1
    nfcv
    nffv
    nfdm
    nfiin
    nfiun
    vy
    @11
    nfcv
    @6
    vy
    nfv
    vx
    @15
    @5
    vx
    @15
    @20
    vm
    vj
    cZ
    @14
    @19
    vj
    @14
    nfcv
    vm
    @13
    @18
    vm
    @17
    cF
    smflim2.n
    vm
    @17
    nfcv
    nffv
    #
    vm
    @13
    nfcv
    nffv
    @1
    @17
    wceq
    #
    @13
    @2
    @18
    @1
    @17
    cF
    fveq2
    #
    fveq1d
    cbvmpt
    #
    vx
    vj
    cZ
    @19
    @27
    vx
    @13
    @18
    vx
    @17
    cF
    smflim2.x
    vx
    @17
    nfcv
    nffv
    vx
    @13
    nfcv
    nffv
    nfmpt
    #
    nfcxfr
    vx
    @5
    nfcv
    nfel
    @0
    @13
    wceq
    #
    @4
    @15
    @5
    @33
    vm
    cZ
    @3
    @14
    @0
    @13
    @2
    fveq2
    mpteq2dv
    #
    eleq1d
    cbvrab
    @16
    @21
    vy
    @11
    @26
    @13
    @11
    wcel
    @13
    @26
    wcel
    @16
    @21
    @11
    @26
    @13
    vn
    vk
    cZ
    @10
    @25
    @7
    @22
    wceq
    #
    @10
    vm
    @23
    @9
    ciin
    #
    @25
    @35
    vm
    @8
    @23
    @9
    @7
    @22
    cuz
    fveq2
    iineq1d
    @36
    @25
    wceq
    @35
    vm
    vj
    @23
    @9
    @24
    vj
    @9
    nfcv
    vm
    @18
    @28
    nfdm
    @29
    @2
    @18
    @30
    dmeqd
    cbviin
    a1i
    eqtrd
    cbviunv
    eleq2i
    @15
    @20
    @5
    @31
    eleq1i
    anbi12i
    rabbia2
    3eqtri
    cG
    vx
    cD
    @4
    cli
    cfv
    #
    cmpt
    vy
    cD
    @20
    cli
    cfv
    #
    cmpt
    smflim2.g
    vx
    vy
    cD
    @37
    @38
    vx
    cD
    @12
    smflim2.d
    @6
    vx
    @11
    nfrab1
    nfcxfr
    vy
    cD
    nfcv
    vy
    @37
    nfcv
    vx
    @20
    cli
    vx
    cli
    nfcv
    @32
    nffv
    @33
    @4
    @20
    cli
    @33
    @4
    @15
    @20
    @34
    @15
    @20
    wceq
    @33
    @31
    a1i
    eqtrd
    fveq2d
    cbvmptf
    eqtri
    smflim
end
