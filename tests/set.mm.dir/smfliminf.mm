include "cv.mm"
include "cfv.mm"
include "cmpt.mm"
include "clsi.mm"
include "cr.mm"
include "wcel.mm"
include "cuz.mm"
include "cdm.mm"
include "ciin.mm"
include "ciun.mm"
include "crab.mm"
include "nfcv.mm"
include "nffv.mm"
include "nfdm.mm"
include "nfiin.mm"
include "nfiun.mm"
include "wceq.mm"
include "fveq2.mm"
include "iineq1d.mm"
include "dmeqd.mm"
include "cbviin.mm"
include "a1i.mm"
include "eqtrd.mm"
include "cbviun.mm"
include "rabeqif.mm"
include "nfv.mm"
include "nfmpt.mm"
include "nfel.mm"
include "adantr.mm"
include "mpteq2da.mm"
include "fveq1d.mm"
include "cbvmpt.mm"
include "fveq2d.mm"
include "eleq1d.mm"
include "cbvrab.mm"
include "3eqtri.mm"
include "nfrab1.mm"
include "nfcxfr.mm"
include "cbvmptf.mm"
include "eqtri.mm"
include "smfliminflem.mm"

theorem smfliminf
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
  let vi: setvar i
  let vk: setvar k
  assume smfliminf.n: |- F/_ m F
  assume smfliminf.x: |- F/_ x F
  assume smfliminf.m: |- ( ph -> M e. ZZ )
  assume smfliminf.z: |- Z = ( ZZ>= ` M )
  assume smfliminf.s: |- ( ph -> S e. SAlg )
  assume smfliminf.f: |- ( ph -> F : Z --> ( SMblFn ` S ) )
  assume smfliminf.d: |- D = { x e. U_ n e. Z |^|_ m e. ( ZZ>= ` n ) dom ( F ` m ) | ( liminf ` ( m e. Z |-> ( ( F ` m ) ` x ) ) ) e. RR }
  assume smfliminf.g: |- G = ( x e. D |-> ( liminf ` ( m e. Z |-> ( ( F ` m ) ` x ) ) ) )

  disjoint F n
  disjoint Z m
  disjoint Z n
  disjoint Z x
  disjoint m n
  disjoint m x
  disjoint n x
  disjoint D y
  disjoint F i
  disjoint F k
  disjoint i k
  disjoint i n
  disjoint k n
  disjoint F y
  disjoint i y
  disjoint k y
  disjoint M k
  disjoint S k
  disjoint Z i
  disjoint Z k
  disjoint i m
  disjoint i x
  disjoint k m
  disjoint k x
  disjoint Z y
  disjoint m y
  disjoint x y
  disjoint i ph
  disjoint k ph
  disjoint ph y
  disjoint k x
  assert |- ( ph -> G e. ( SMblFn ` S ) )

  proof
    wph
    vy
    cD
    cS
    vk
    vi
    cF
    cG
    cM
    cZ
    smfliminf.m
    smfliminf.z
    smfliminf.s
    smfliminf.f
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
    clsi
    cfv
    #
    cr
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
    @6
    vx
    vi
    cZ
    vk
    vi
    cv
    #
    cuz
    cfv
    #
    vk
    cv
    #
    cF
    cfv
    #
    cdm
    #
    ciin
    #
    ciun
    #
    crab
    vk
    cZ
    vy
    cv
    #
    @16
    cfv
    #
    cmpt
    #
    clsi
    cfv
    #
    cr
    wcel
    #
    vy
    @19
    crab
    smfliminf.d
    @6
    vx
    @11
    @19
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
    smfliminf.x
    vx
    @1
    nfcv
    nffv
    nfdm
    nfiin
    nfiun
    vi
    vx
    cZ
    @18
    @25
    vk
    vx
    @14
    @17
    vx
    @14
    nfcv
    vx
    @16
    vx
    @15
    cF
    smfliminf.x
    vx
    @15
    nfcv
    nffv
    #
    nfdm
    nfiin
    nfiun
    #
    vn
    vi
    cZ
    @10
    @18
    vi
    @10
    nfcv
    vn
    @18
    nfcv
    @7
    @13
    wceq
    #
    @10
    vm
    @14
    @9
    ciin
    #
    @18
    @28
    vm
    @8
    @14
    @9
    @7
    @13
    cuz
    fveq2
    iineq1d
    @29
    @18
    wceq
    @28
    vm
    vk
    @14
    @9
    @17
    vk
    @2
    vk
    @2
    nfcv
    nfdm
    vm
    @16
    vm
    @15
    cF
    smfliminf.n
    vm
    @15
    nfcv
    nffv
    #
    nfdm
    @1
    @15
    wceq
    #
    @2
    @16
    @1
    @15
    cF
    fveq2
    #
    dmeqd
    cbviin
    a1i
    eqtrd
    cbviun
    rabeqif
    @6
    @24
    vx
    vy
    @19
    @27
    vy
    @19
    nfcv
    @6
    vy
    nfv
    vx
    @23
    cr
    vx
    @22
    clsi
    vx
    clsi
    nfcv
    vx
    vk
    cZ
    @21
    @25
    vx
    @20
    @16
    @26
    vx
    @20
    nfcv
    nffv
    nfmpt
    nffv
    #
    vx
    cr
    nfcv
    nfel
    @0
    @20
    wceq
    #
    @5
    @23
    cr
    @34
    @4
    @22
    clsi
    @34
    @4
    vm
    cZ
    @20
    @2
    cfv
    #
    cmpt
    #
    @22
    @34
    vm
    cZ
    @3
    @35
    @34
    vm
    nfv
    @34
    @3
    @35
    wceq
    @1
    cZ
    wcel
    @0
    @20
    @2
    fveq2
    adantr
    mpteq2da
    @36
    @22
    wceq
    @34
    vm
    vk
    cZ
    @35
    @21
    vk
    @35
    nfcv
    vm
    @20
    @16
    @30
    vm
    @20
    nfcv
    nffv
    @31
    @20
    @2
    @16
    @32
    fveq1d
    cbvmpt
    a1i
    eqtrd
    fveq2d
    #
    eleq1d
    cbvrab
    3eqtri
    cG
    vx
    cD
    @5
    cmpt
    vy
    cD
    @23
    cmpt
    smfliminf.g
    vx
    vy
    cD
    @5
    @23
    vx
    cD
    @12
    smfliminf.d
    @6
    vx
    @11
    nfrab1
    nfcxfr
    vy
    cD
    nfcv
    vy
    @5
    nfcv
    @33
    @37
    cbvmptf
    eqtri
    smfliminflem
end
