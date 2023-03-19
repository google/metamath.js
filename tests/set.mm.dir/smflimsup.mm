include "cv.mm"
include "cuz.mm"
include "cfv.mm"
include "cmpt.mm"
include "crn.mm"
include "cxr.mm"
include "clt.mm"
include "csup.mm"
include "cr.mm"
include "wcel.mm"
include "cdm.mm"
include "ciin.mm"
include "crab.mm"
include "clsp.mm"
include "ciun.mm"
include "wceq.mm"
include "fveq2.mm"
include "iineq1d.mm"
include "nfcv.mm"
include "nffv.mm"
include "nfdm.mm"
include "dmeqd.mm"
include "cbviin.mm"
include "a1i.mm"
include "eqtrd.mm"
include "cbviunv.mm"
include "eleq2i.mm"
include "fveq1d.mm"
include "cbvmpt.mm"
include "fveq2i.mm"
include "eleq1i.mm"
include "anbi12i.mm"
include "rabbia2.mm"
include "nfiin.mm"
include "nfiun.mm"
include "nfv.mm"
include "nfmpt.mm"
include "nfel.mm"
include "mpteq2dv.mm"
include "fveq2d.mm"
include "eleq1d.mm"
include "cbvrab.mm"
include "3eqtri.mm"
include "mpteq2i.mm"
include "nfrab1.mm"
include "nfcxfr.mm"
include "cbvmptf.mm"
include "nfrn.mm"
include "nfsup.mm"
include "rneqd.mm"
include "supeq1d.mm"
include "eleq2d.mm"
include "mpteq1d.mm"
include "anbi12d.mm"
include "rabbidva2.mm"
include "cbvmptv.mm"
include "cbviinv.mm"
include "rneqi.mm"
include "supeq1i.mm"
include "fveq1i.mm"
include "mpteq12i.mm"
include "eqtri.mm"
include "mpteq12dv.mm"
include "smflimsuplem8.mm"

theorem smflimsup
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
  let vj: setvar j
  let vk: setvar k
  let vq: setvar q
  let vw: setvar w
  let vi: setvar i
  let vl: setvar l
  let vp: setvar p
  let vy: setvar y
  assume smflimsup.n: |- F/_ m F
  assume smflimsup.x: |- F/_ x F
  assume smflimsup.m: |- ( ph -> M e. ZZ )
  assume smflimsup.z: |- Z = ( ZZ>= ` M )
  assume smflimsup.s: |- ( ph -> S e. SAlg )
  assume smflimsup.f: |- ( ph -> F : Z --> ( SMblFn ` S ) )
  assume smflimsup.d: |- D = { x e. U_ n e. Z |^|_ m e. ( ZZ>= ` n ) dom ( F ` m ) | ( limsup ` ( m e. Z |-> ( ( F ` m ) ` x ) ) ) e. RR }
  assume smflimsup.g: |- G = ( x e. D |-> ( limsup ` ( m e. Z |-> ( ( F ` m ) ` x ) ) ) )

  disjoint F n
  disjoint Z x
  disjoint Z m
  disjoint Z n
  disjoint m n
  disjoint m x
  disjoint D j
  disjoint D k
  disjoint D q
  disjoint D w
  disjoint j k
  disjoint j q
  disjoint j w
  disjoint k q
  disjoint k w
  disjoint q w
  disjoint F i
  disjoint F j
  disjoint F k
  disjoint F l
  disjoint F p
  disjoint F q
  disjoint F w
  disjoint F y
  disjoint i j
  disjoint i k
  disjoint i l
  disjoint i p
  disjoint i q
  disjoint i w
  disjoint i y
  disjoint j l
  disjoint j p
  disjoint j y
  disjoint k l
  disjoint k p
  disjoint k y
  disjoint l p
  disjoint l q
  disjoint l w
  disjoint l y
  disjoint p q
  disjoint p w
  disjoint p y
  disjoint q y
  disjoint w y
  disjoint j n
  disjoint n q
  disjoint M q
  disjoint S j
  disjoint S k
  disjoint Z i
  disjoint Z j
  disjoint Z k
  disjoint Z l
  disjoint Z q
  disjoint Z w
  disjoint Z y
  disjoint i x
  disjoint j x
  disjoint k x
  disjoint l x
  disjoint q x
  disjoint w x
  disjoint x y
  disjoint j m
  disjoint m q
  disjoint j ph
  disjoint k ph
  disjoint ph q
  disjoint ph w
  disjoint p x
  disjoint k x
  assert |- ( ph -> G e. ( SMblFn ` S ) )

  proof
    wph
    vw
    cD
    cS
    vk
    vq
    vj
    vi
    cZ
    vq
    vi
    cv
    #
    cuz
    cfv
    #
    vx
    cv
    #
    vq
    cv
    #
    cF
    cfv
    #
    cfv
    #
    cmpt
    #
    crn
    #
    cxr
    clt
    csup
    #
    cr
    wcel
    #
    vx
    vq
    @1
    @4
    cdm
    #
    ciin
    #
    crab
    #
    cmpt
    #
    cF
    cG
    vl
    cZ
    vy
    vl
    cv
    #
    vi
    cZ
    vp
    @1
    @2
    vp
    cv
    #
    cF
    cfv
    #
    cfv
    #
    cmpt
    #
    crn
    #
    cxr
    clt
    csup
    #
    cr
    wcel
    #
    vx
    vp
    @1
    @16
    cdm
    #
    ciin
    #
    crab
    #
    cmpt
    #
    cfv
    #
    vp
    @14
    cuz
    cfv
    #
    vy
    cv
    #
    @16
    cfv
    #
    cmpt
    #
    crn
    #
    cxr
    clt
    csup
    #
    cmpt
    #
    cmpt
    cM
    cZ
    smflimsup.m
    smflimsup.z
    smflimsup.s
    smflimsup.f
    cD
    vm
    cZ
    @2
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
    clsp
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
    @35
    cdm
    #
    ciin
    #
    ciun
    #
    crab
    #
    vq
    cZ
    @5
    cmpt
    #
    clsp
    cfv
    #
    cr
    wcel
    #
    vx
    vj
    cZ
    vq
    vj
    cv
    #
    cuz
    cfv
    #
    @10
    ciin
    #
    ciun
    #
    crab
    vq
    cZ
    vw
    cv
    #
    @4
    cfv
    #
    cmpt
    #
    clsp
    cfv
    #
    cr
    wcel
    #
    vw
    @52
    crab
    smflimsup.d
    @39
    @48
    vx
    @44
    @52
    @2
    @44
    wcel
    @2
    @52
    wcel
    @39
    @48
    @44
    @52
    @2
    vn
    vj
    cZ
    @43
    @51
    @40
    @49
    wceq
    #
    @43
    vm
    @50
    @42
    ciin
    #
    @51
    @58
    vm
    @41
    @50
    @42
    @40
    @49
    cuz
    fveq2
    iineq1d
    @59
    @51
    wceq
    @58
    vm
    vq
    @50
    @42
    @10
    vq
    @42
    nfcv
    vm
    @4
    vm
    @3
    cF
    smflimsup.n
    vm
    @3
    nfcv
    nffv
    #
    nfdm
    @34
    @3
    wceq
    #
    @35
    @4
    @34
    @3
    cF
    fveq2
    #
    dmeqd
    cbviin
    a1i
    eqtrd
    cbviunv
    eleq2i
    @38
    @47
    cr
    @37
    @46
    clsp
    vm
    vq
    cZ
    @36
    @5
    vq
    @36
    nfcv
    vm
    @2
    @4
    @60
    vm
    @2
    nfcv
    nffv
    @61
    @2
    @35
    @4
    @62
    fveq1d
    cbvmpt
    fveq2i
    #
    eleq1i
    anbi12i
    rabbia2
    @48
    @57
    vx
    vw
    @52
    vj
    vx
    cZ
    @51
    vx
    cZ
    nfcv
    #
    vq
    vx
    @50
    @10
    vx
    @50
    nfcv
    vx
    @4
    vx
    @3
    cF
    smflimsup.x
    vx
    @3
    nfcv
    nffv
    #
    nfdm
    #
    nfiin
    nfiun
    vw
    @52
    nfcv
    @48
    vw
    nfv
    vx
    @56
    cr
    vx
    @55
    clsp
    vx
    clsp
    nfcv
    vx
    vq
    cZ
    @54
    @64
    vx
    @53
    @4
    @65
    vx
    @53
    nfcv
    nffv
    #
    nfmpt
    nffv
    #
    vx
    cr
    nfcv
    #
    nfel
    @2
    @53
    wceq
    #
    @47
    @56
    cr
    @70
    @46
    @55
    clsp
    @70
    vq
    cZ
    @5
    @54
    @2
    @53
    @4
    fveq2
    #
    mpteq2dv
    fveq2d
    #
    eleq1d
    cbvrab
    3eqtri
    cG
    vx
    cD
    @38
    cmpt
    vx
    cD
    @47
    cmpt
    vw
    cD
    @56
    cmpt
    smflimsup.g
    vx
    cD
    @38
    @47
    @63
    mpteq2i
    vx
    vw
    cD
    @47
    @56
    vx
    cD
    @45
    smflimsup.d
    @39
    vx
    @44
    nfrab1
    nfcxfr
    vw
    cD
    nfcv
    vw
    @47
    nfcv
    @68
    @72
    cbvmptf
    3eqtri
    vi
    vk
    cZ
    @12
    vq
    vk
    cv
    #
    cuz
    cfv
    #
    @54
    cmpt
    #
    crn
    #
    cxr
    clt
    csup
    #
    cr
    wcel
    #
    vw
    vq
    @74
    @10
    ciin
    #
    crab
    #
    @0
    @73
    wceq
    #
    @12
    vq
    @1
    @54
    cmpt
    #
    crn
    #
    cxr
    clt
    csup
    #
    cr
    wcel
    #
    vw
    @11
    crab
    #
    @80
    @12
    @86
    wceq
    @81
    @9
    @85
    vx
    vw
    @11
    vq
    vx
    @1
    @10
    vx
    @1
    nfcv
    #
    @66
    nfiin
    vw
    @11
    nfcv
    @9
    vw
    nfv
    vx
    @84
    cr
    vx
    @83
    cxr
    clt
    vx
    @82
    vx
    vq
    @1
    @54
    @87
    @67
    nfmpt
    nfrn
    vx
    cxr
    nfcv
    vx
    clt
    nfcv
    nfsup
    @69
    nfel
    @70
    @8
    @84
    cr
    @70
    cxr
    @7
    @83
    clt
    @70
    @6
    @82
    @70
    vq
    @1
    @5
    @54
    @71
    mpteq2dv
    rneqd
    supeq1d
    eleq1d
    cbvrab
    a1i
    @81
    @85
    @78
    vw
    @11
    @79
    @81
    @53
    @11
    wcel
    @53
    @79
    wcel
    @85
    @78
    @81
    @11
    @79
    @53
    @81
    vq
    @1
    @74
    @10
    @0
    @73
    cuz
    fveq2
    #
    iineq1d
    eleq2d
    @81
    @84
    @77
    cr
    @81
    cxr
    @83
    @76
    clt
    @81
    @82
    @75
    @81
    vq
    @1
    @74
    @54
    @88
    mpteq1d
    rneqd
    supeq1d
    eleq1d
    anbi12d
    rabbidva2
    eqtrd
    cbvmptv
    vl
    vk
    cZ
    @33
    vw
    @73
    @13
    cfv
    #
    @77
    cmpt
    #
    @14
    @73
    wceq
    #
    @33
    vw
    @14
    @13
    cfv
    #
    vq
    @27
    @54
    cmpt
    #
    crn
    #
    cxr
    clt
    csup
    #
    cmpt
    #
    @90
    @33
    @96
    wceq
    @91
    @33
    vw
    @26
    vp
    @27
    @53
    @16
    cfv
    #
    cmpt
    #
    crn
    #
    cxr
    clt
    csup
    #
    cmpt
    @96
    vy
    vw
    @26
    @32
    @100
    @28
    @53
    wceq
    #
    cxr
    @31
    @99
    clt
    @101
    @30
    @98
    @101
    vp
    @27
    @29
    @97
    @28
    @53
    @16
    fveq2
    mpteq2dv
    rneqd
    supeq1d
    cbvmptv
    vw
    @26
    @100
    @92
    @95
    @14
    @25
    @13
    vi
    cZ
    @24
    @12
    @21
    @9
    vx
    @23
    @11
    @2
    @23
    wcel
    @2
    @11
    wcel
    @21
    @9
    @23
    @11
    @2
    vp
    vq
    @1
    @22
    @10
    @15
    @3
    wceq
    #
    @16
    @4
    @15
    @3
    cF
    fveq2
    #
    dmeqd
    cbviinv
    eleq2i
    @20
    @8
    cr
    cxr
    @19
    @7
    clt
    @18
    @6
    vp
    vq
    @1
    @17
    @5
    vq
    @17
    nfcv
    vp
    @2
    @4
    vp
    @4
    nfcv
    vp
    @2
    nfcv
    nffv
    @102
    @2
    @16
    @4
    @103
    fveq1d
    cbvmpt
    rneqi
    supeq1i
    eleq1i
    anbi12i
    rabbia2
    mpteq2i
    fveq1i
    cxr
    @99
    @94
    clt
    @98
    @93
    vp
    vq
    @27
    @97
    @54
    @102
    @53
    @16
    @4
    @103
    fveq1d
    cbvmptv
    rneqi
    supeq1i
    mpteq12i
    eqtri
    a1i
    @91
    vw
    @92
    @95
    @89
    @77
    @14
    @73
    @13
    fveq2
    @91
    cxr
    @94
    @76
    clt
    @91
    @93
    @75
    @91
    vq
    @27
    @74
    @54
    @14
    @73
    cuz
    fveq2
    mpteq1d
    rneqd
    supeq1d
    mpteq12dv
    eqtrd
    cbvmptv
    smflimsuplem8
end
