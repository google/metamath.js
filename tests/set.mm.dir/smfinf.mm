include "cv.mm"
include "cfv.mm"
include "cle.mm"
include "wbr.mm"
include "wral.mm"
include "cr.mm"
include "wrex.mm"
include "cdm.mm"
include "ciin.mm"
include "crab.mm"
include "nfcv.mm"
include "nffv.mm"
include "nfdm.mm"
include "nfiin.mm"
include "nfv.mm"
include "nfbr.mm"
include "nfral.mm"
include "nfrex.mm"
include "wceq.mm"
include "fveq2.mm"
include "dmeqd.mm"
include "cbviin.mm"
include "a1i.mm"
include "breq2d.mm"
include "ralbidv.mm"
include "wb.mm"
include "fveq1d.mm"
include "cbvral.mm"
include "bitrd.mm"
include "rexbidv.mm"
include "breq1.mm"
include "cbvrexv.mm"
include "cbvrabcsf.mm"
include "eqtri.mm"
include "cmpt.mm"
include "crn.mm"
include "clt.mm"
include "cinf.mm"
include "nfrab1.mm"
include "nfcxfr.mm"
include "nfmpt.mm"
include "nfrn.mm"
include "nfinf.mm"
include "mpteq2dv.mm"
include "cbvmpt.mm"
include "eqtrd.mm"
include "rneqd.mm"
include "infeq1d.mm"
include "cbvmptf.mm"
include "smfinflem.mm"

theorem smfinf
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let cD: class D
  let cS: class S
  let vn: setvar n
  let cF: class F
  let cG: class G
  let cM: class M
  let cZ: class Z
  let vm: setvar m
  let vw: setvar w
  let vz: setvar z
  let vk: setvar k
  assume smfinf.n: |- F/_ n F
  assume smfinf.x: |- F/_ x F
  assume smfinf.m: |- ( ph -> M e. ZZ )
  assume smfinf.z: |- Z = ( ZZ>= ` M )
  assume smfinf.s: |- ( ph -> S e. SAlg )
  assume smfinf.f: |- ( ph -> F : Z --> ( SMblFn ` S ) )
  assume smfinf.d: |- D = { x e. |^|_ n e. Z dom ( F ` n ) | E. y e. RR A. n e. Z y <_ ( ( F ` n ) ` x ) }
  assume smfinf.g: |- G = ( x e. D |-> inf ( ran ( n e. Z |-> ( ( F ` n ) ` x ) ) , RR , < ) )

  disjoint F y
  disjoint Z n
  disjoint Z x
  disjoint Z y
  disjoint n x
  disjoint n y
  disjoint x y
  disjoint D m
  disjoint D w
  disjoint D z
  disjoint m w
  disjoint m z
  disjoint w z
  disjoint F m
  disjoint F w
  disjoint F z
  disjoint m y
  disjoint w y
  disjoint y z
  disjoint S m
  disjoint Z m
  disjoint Z w
  disjoint m n
  disjoint m x
  disjoint n w
  disjoint w x
  disjoint Z z
  disjoint x z
  disjoint m ph
  disjoint ph w
  disjoint ph z
  disjoint k x
  assert |- ( ph -> G e. ( SMblFn ` S ) )

  proof
    wph
    vw
    vz
    cD
    cS
    vm
    cF
    cG
    cM
    cZ
    smfinf.m
    smfinf.z
    smfinf.s
    smfinf.f
    cD
    vy
    cv
    #
    vx
    cv
    #
    vn
    cv
    #
    cF
    cfv
    #
    cfv
    #
    cle
    wbr
    #
    vn
    cZ
    wral
    #
    vy
    cr
    wrex
    #
    vx
    vn
    cZ
    @3
    cdm
    #
    ciin
    #
    crab
    #
    vz
    cv
    #
    vw
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
    cle
    wbr
    #
    vm
    cZ
    wral
    #
    vz
    cr
    wrex
    #
    vw
    vm
    cZ
    @14
    cdm
    #
    ciin
    #
    crab
    smfinf.d
    @7
    @18
    vx
    vw
    @9
    @20
    vw
    @9
    nfcv
    vm
    vx
    cZ
    @19
    vx
    cZ
    nfcv
    #
    vx
    @14
    vx
    @13
    cF
    smfinf.x
    vx
    @13
    nfcv
    nffv
    #
    nfdm
    nfiin
    @7
    vw
    nfv
    @17
    vx
    vz
    cr
    vx
    cr
    nfcv
    #
    @16
    vx
    vm
    cZ
    @21
    vx
    @11
    @15
    cle
    vx
    @11
    nfcv
    vx
    cle
    nfcv
    vx
    @12
    @14
    @22
    vx
    @12
    nfcv
    nffv
    #
    nfbr
    nfral
    nfrex
    @9
    @20
    wceq
    @1
    @12
    wceq
    #
    vn
    vm
    cZ
    @8
    @19
    vm
    @8
    nfcv
    vn
    @14
    vn
    @13
    cF
    smfinf.n
    vn
    @13
    nfcv
    nffv
    #
    nfdm
    @2
    @13
    wceq
    #
    @3
    @14
    @2
    @13
    cF
    fveq2
    #
    dmeqd
    cbviin
    a1i
    @25
    @7
    @0
    @15
    cle
    wbr
    #
    vm
    cZ
    wral
    #
    vy
    cr
    wrex
    #
    @18
    @25
    @6
    @30
    vy
    cr
    @25
    @6
    @0
    @12
    @3
    cfv
    #
    cle
    wbr
    #
    vn
    cZ
    wral
    #
    @30
    @25
    @5
    @33
    vn
    cZ
    @25
    @4
    @32
    @0
    cle
    @1
    @12
    @3
    fveq2
    #
    breq2d
    ralbidv
    @34
    @30
    wb
    @25
    @33
    @29
    vn
    vm
    cZ
    @33
    vm
    nfv
    vn
    @0
    @15
    cle
    vn
    @0
    nfcv
    vn
    cle
    nfcv
    vn
    @12
    @14
    @26
    vn
    @12
    nfcv
    nffv
    #
    nfbr
    @27
    @32
    @15
    @0
    cle
    @27
    @12
    @3
    @14
    @28
    fveq1d
    #
    breq2d
    cbvral
    a1i
    bitrd
    rexbidv
    @31
    @18
    wb
    @25
    @30
    @17
    vy
    vz
    cr
    @0
    @11
    wceq
    @29
    @16
    vm
    cZ
    @0
    @11
    @15
    cle
    breq1
    ralbidv
    cbvrexv
    a1i
    bitrd
    cbvrabcsf
    eqtri
    cG
    vx
    cD
    vn
    cZ
    @4
    cmpt
    #
    crn
    #
    cr
    clt
    cinf
    #
    cmpt
    vw
    cD
    vm
    cZ
    @15
    cmpt
    #
    crn
    #
    cr
    clt
    cinf
    #
    cmpt
    smfinf.g
    vx
    vw
    cD
    @40
    @43
    vx
    cD
    @10
    smfinf.d
    @7
    vx
    @9
    nfrab1
    nfcxfr
    vw
    cD
    nfcv
    vw
    @40
    nfcv
    vx
    @42
    cr
    clt
    vx
    @41
    vx
    vm
    cZ
    @15
    @21
    @24
    nfmpt
    nfrn
    @23
    vx
    clt
    nfcv
    nfinf
    @25
    cr
    @39
    @42
    clt
    @25
    @38
    @41
    @25
    @38
    vn
    cZ
    @32
    cmpt
    #
    @41
    @25
    vn
    cZ
    @4
    @32
    @35
    mpteq2dv
    @44
    @41
    wceq
    @25
    vn
    vm
    cZ
    @32
    @15
    vm
    @32
    nfcv
    @36
    @37
    cbvmpt
    a1i
    eqtrd
    rneqd
    infeq1d
    cbvmptf
    eqtri
    smfinflem
end
