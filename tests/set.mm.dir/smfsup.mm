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
include "breq1d.mm"
include "ralbidv.mm"
include "wb.mm"
include "fveq1d.mm"
include "cbvral.mm"
include "bitrd.mm"
include "rexbidv.mm"
include "breq2.mm"
include "cbvrexv.mm"
include "cbvrabcsf.mm"
include "eqtri.mm"
include "cmpt.mm"
include "crn.mm"
include "clt.mm"
include "csup.mm"
include "nfrab1.mm"
include "nfcxfr.mm"
include "nfmpt.mm"
include "nfrn.mm"
include "nfsup.mm"
include "mpteq2dv.mm"
include "cbvmpt.mm"
include "eqtrd.mm"
include "rneqd.mm"
include "supeq1d.mm"
include "cbvmptf.mm"
include "smfsuplem3.mm"

theorem smfsup
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
  assume smfsup.n: |- F/_ n F
  assume smfsup.x: |- F/_ x F
  assume smfsup.m: |- ( ph -> M e. ZZ )
  assume smfsup.z: |- Z = ( ZZ>= ` M )
  assume smfsup.s: |- ( ph -> S e. SAlg )
  assume smfsup.f: |- ( ph -> F : Z --> ( SMblFn ` S ) )
  assume smfsup.d: |- D = { x e. |^|_ n e. Z dom ( F ` n ) | E. y e. RR A. n e. Z ( ( F ` n ) ` x ) <_ y }
  assume smfsup.g: |- G = ( x e. D |-> sup ( ran ( n e. Z |-> ( ( F ` n ) ` x ) ) , RR , < ) )

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
  disjoint M m
  disjoint S m
  disjoint S z
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
    smfsup.m
    smfsup.z
    smfsup.s
    smfsup.f
    cD
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
    vy
    cv
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
    @2
    cdm
    #
    ciin
    #
    crab
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
    vz
    cv
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
    @13
    cdm
    #
    ciin
    #
    crab
    smfsup.d
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
    @13
    vx
    @12
    cF
    smfsup.x
    vx
    @12
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
    @14
    @15
    cle
    vx
    @11
    @13
    @22
    vx
    @11
    nfcv
    nffv
    #
    vx
    cle
    nfcv
    vx
    @15
    nfcv
    nfbr
    nfral
    nfrex
    @9
    @20
    wceq
    @0
    @11
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
    @13
    vn
    @12
    cF
    smfsup.n
    vn
    @12
    nfcv
    nffv
    #
    nfdm
    @1
    @12
    wceq
    #
    @2
    @13
    @1
    @12
    cF
    fveq2
    #
    dmeqd
    cbviin
    a1i
    @25
    @7
    @14
    @4
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
    @11
    @2
    cfv
    #
    @4
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
    @3
    @32
    @4
    cle
    @0
    @11
    @2
    fveq2
    #
    breq1d
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
    @14
    @4
    cle
    vn
    @11
    @13
    @26
    vn
    @11
    nfcv
    nffv
    #
    vn
    cle
    nfcv
    vn
    @4
    nfcv
    nfbr
    @27
    @32
    @14
    @4
    cle
    @27
    @11
    @2
    @13
    @28
    fveq1d
    #
    breq1d
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
    @4
    @15
    wceq
    @29
    @16
    vm
    cZ
    @4
    @15
    @14
    cle
    breq2
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
    @3
    cmpt
    #
    crn
    #
    cr
    clt
    csup
    #
    cmpt
    vw
    cD
    vm
    cZ
    @14
    cmpt
    #
    crn
    #
    cr
    clt
    csup
    #
    cmpt
    smfsup.g
    vx
    vw
    cD
    @40
    @43
    vx
    cD
    @10
    smfsup.d
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
    @14
    @21
    @24
    nfmpt
    nfrn
    @23
    vx
    clt
    nfcv
    nfsup
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
    @3
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
    @14
    vm
    @32
    nfcv
    @36
    @37
    cbvmpt
    a1i
    eqtrd
    rneqd
    supeq1d
    cbvmptf
    eqtri
    smfsuplem3
end
