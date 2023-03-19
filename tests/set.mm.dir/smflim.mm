include "nfv.mm"
include "cv.mm"
include "cuz.mm"
include "cfv.mm"
include "cdm.mm"
include "ciin.mm"
include "ciun.mm"
include "cuni.mm"
include "wss.mm"
include "cmpt.mm"
include "cli.mm"
include "wcel.mm"
include "crab.mm"
include "nfcv.mm"
include "nffv.mm"
include "nfdm.mm"
include "nfiin.mm"
include "nfiun.mm"
include "ssrab2f.mm"
include "eqsstri.mm"
include "a1i.mm"
include "wa.mm"
include "wrex.mm"
include "cz.mm"
include "uzssz.mm"
include "eleq2i.mm"
include "biimpi.mm"
include "sseldi.mm"
include "uzid.mm"
include "syl.mm"
include "adantl.mm"
include "csalg.mm"
include "adantr.mm"
include "csmblfn.mm"
include "ffvelrnda.mm"
include "eqid.mm"
include "smfdmss.mm"
include "nfss.mm"
include "wceq.mm"
include "fveq2.mm"
include "dmeqd.mm"
include "sseq1d.mm"
include "rspce.mm"
include "syl2anc.mm"
include "iinss.mm"
include "iunssd.mm"
include "sstrd.mm"
include "cr.mm"
include "nfmpt1.mm"
include "nfel.mm"
include "nfii1.mm"
include "nfrab.mm"
include "nfcxfr.mm"
include "nfan.mm"
include "wf.mm"
include "smff.mm"
include "adantlr.mm"
include "nfmpt.mm"
include "nfel1.mm"
include "mpteq2dv.mm"
include "eleq1d.mm"
include "cbvrab.mm"
include "cbviin.mm"
include "eqidd.mm"
include "iineq12dv.mm"
include "eqtrd.mm"
include "cbviunv.mm"
include "fveq1d.mm"
include "cbvmptf.mm"
include "eleq1i.mm"
include "anbi12i.mm"
include "rabbia2.mm"
include "3eqtri.mm"
include "cbvrabv.mm"
include "iuneq2i.mm"
include "eqtri.mm"
include "simpr.mm"
include "fnlimfvre.mm"
include "nfrab1.mm"
include "fveq2d.mm"
include "fmptd.mm"
include "cn.mm"
include "c1.mm"
include "cdiv.mm"
include "co.mm"
include "caddc.mm"
include "clt.mm"
include "wbr.mm"
include "cin.mm"
include "cmpt2.mm"
include "simpl.mm"
include "mpteq2dva.mm"
include "nfbr.mm"
include "nfin.mm"
include "nfeq.mm"
include "breq1d.mm"
include "ineq1.mm"
include "eqeq12d.mm"
include "eleq2d.mm"
include "anbi12d.mm"
include "rabbidva2.mm"
include "ineq2d.mm"
include "rabbidv.mm"
include "oveq2.mm"
include "oveq2d.mm"
include "breq2d.mm"
include "eqeq1d.mm"
include "sylan9eq.mm"
include "cbvmpt2.mm"
include "eqcomi.mm"
include "smflimlem6.mm"
include "issmfled.mm"

theorem smflim
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
  let vi: setvar i
  let vj: setvar j
  let vl: setvar l
  let vy: setvar y
  let vk: setvar k
  let vs: setvar s
  let vt: setvar t
  let vw: setvar w
  let va: setvar a
  assume smflim.n: |- F/_ m F
  assume smflim.x: |- F/_ x F
  assume smflim.m: |- ( ph -> M e. ZZ )
  assume smflim.z: |- Z = ( ZZ>= ` M )
  assume smflim.s: |- ( ph -> S e. SAlg )
  assume smflim.f: |- ( ph -> F : Z --> ( SMblFn ` S ) )
  assume smflim.d: |- D = { x e. U_ n e. Z |^|_ m e. ( ZZ>= ` n ) dom ( F ` m ) | ( m e. Z |-> ( ( F ` m ) ` x ) ) e. dom ~~> }
  assume smflim.g: |- G = ( x e. D |-> ( ~~> ` ( m e. Z |-> ( ( F ` m ) ` x ) ) ) )

  disjoint F n
  disjoint S m
  disjoint S n
  disjoint m n
  disjoint Z m
  disjoint Z x
  disjoint m x
  disjoint Z n
  disjoint n x
  disjoint m ph
  disjoint n ph
  disjoint D i
  disjoint D j
  disjoint D l
  disjoint D y
  disjoint i j
  disjoint i l
  disjoint i y
  disjoint j l
  disjoint j y
  disjoint l y
  disjoint F i
  disjoint F j
  disjoint F k
  disjoint F l
  disjoint F s
  disjoint F y
  disjoint i k
  disjoint i s
  disjoint j k
  disjoint j s
  disjoint k l
  disjoint k s
  disjoint k y
  disjoint l s
  disjoint s y
  disjoint i n
  disjoint l n
  disjoint n y
  disjoint F t
  disjoint j t
  disjoint k t
  disjoint l t
  disjoint s t
  disjoint t y
  disjoint F w
  disjoint i w
  disjoint l w
  disjoint w y
  disjoint G a
  disjoint G i
  disjoint G j
  disjoint G l
  disjoint G y
  disjoint a i
  disjoint a j
  disjoint a l
  disjoint a y
  disjoint M l
  disjoint S a
  disjoint S i
  disjoint S j
  disjoint S k
  disjoint S l
  disjoint S s
  disjoint S y
  disjoint a k
  disjoint a m
  disjoint a s
  disjoint i m
  disjoint j m
  disjoint k m
  disjoint l m
  disjoint m s
  disjoint m y
  disjoint S t
  disjoint a t
  disjoint m t
  disjoint Z i
  disjoint Z j
  disjoint Z k
  disjoint Z l
  disjoint Z y
  disjoint i x
  disjoint j x
  disjoint k x
  disjoint l x
  disjoint x y
  disjoint Z t
  disjoint t x
  disjoint Z w
  disjoint m w
  disjoint a ph
  disjoint i ph
  disjoint j ph
  disjoint l ph
  disjoint ph y
  disjoint a x
  disjoint k x
  assert |- ( ph -> G e. ( SMblFn ` S ) )

  proof
    wph
    vy
    cD
    cS
    cG
    va
    wph
    va
    nfv
    smflim.s
    wph
    cD
    vn
    cZ
    vm
    vn
    cv
    #
    cuz
    cfv
    #
    vm
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
    cS
    cuni
    #
    cD
    @6
    wss
    wph
    cD
    vm
    cZ
    vx
    cv
    #
    @3
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
    @6
    crab
    #
    @6
    smflim.d
    @12
    vx
    @6
    vn
    vx
    cZ
    @5
    vx
    cZ
    nfcv
    #
    vm
    vx
    @1
    @4
    vx
    @1
    nfcv
    vx
    @3
    vx
    @2
    cF
    smflim.x
    vx
    @2
    nfcv
    nffv
    #
    nfdm
    nfiin
    nfiun
    #
    ssrab2f
    eqsstri
    a1i
    wph
    vn
    cZ
    @5
    @7
    wph
    @0
    cZ
    wcel
    #
    wa
    #
    @4
    @7
    wss
    #
    vm
    @1
    wrex
    #
    @5
    @7
    wss
    @18
    @0
    @1
    wcel
    #
    @0
    cF
    cfv
    #
    cdm
    #
    @7
    wss
    #
    @20
    @17
    @21
    wph
    @17
    @0
    cz
    wcel
    @21
    @17
    cM
    cuz
    cfv
    #
    cz
    @0
    cM
    uzssz
    @17
    @0
    @25
    wcel
    cZ
    @25
    @0
    smflim.z
    eleq2i
    biimpi
    sseldi
    @0
    uzid
    syl
    adantl
    @18
    @23
    cS
    @22
    wph
    cS
    csalg
    wcel
    #
    @17
    smflim.s
    adantr
    wph
    cZ
    cS
    csmblfn
    cfv
    #
    @0
    cF
    smflim.f
    ffvelrnda
    @23
    eqid
    smfdmss
    @19
    @24
    vm
    @0
    @1
    vm
    @23
    @7
    vm
    @22
    vm
    @0
    cF
    smflim.n
    vm
    @0
    nfcv
    nffv
    nfdm
    vm
    @7
    nfcv
    nfss
    @2
    @0
    wceq
    #
    @4
    @23
    @7
    @28
    @3
    @22
    @2
    @0
    cF
    fveq2
    dmeqd
    sseq1d
    rspce
    syl2anc
    vm
    @1
    @4
    @7
    iinss
    syl
    iunssd
    sstrd
    wph
    vy
    cD
    vm
    cZ
    vy
    cv
    #
    @3
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
    @29
    cD
    wcel
    #
    wa
    vw
    cD
    vm
    vi
    cF
    cM
    @29
    cZ
    wph
    @33
    vm
    wph
    vm
    nfv
    vm
    @29
    cD
    vm
    @29
    nfcv
    #
    vm
    cD
    @13
    smflim.d
    @12
    vm
    vx
    @6
    vm
    @10
    @11
    vm
    cZ
    @9
    nfmpt1
    vm
    @11
    nfcv
    nfel
    vn
    vm
    cZ
    @5
    vm
    cZ
    nfcv
    #
    vm
    @1
    @4
    nfii1
    nfiun
    nfrab
    nfcxfr
    nfel
    nfan
    smflim.n
    vw
    cF
    nfcv
    smflim.z
    wph
    @2
    cZ
    wcel
    #
    @4
    cr
    @3
    wf
    @33
    wph
    @36
    wa
    @4
    cS
    @3
    wph
    @26
    @36
    smflim.s
    adantr
    wph
    cZ
    @27
    @2
    cF
    smflim.f
    ffvelrnda
    @4
    eqid
    smff
    adantlr
    cD
    vl
    cZ
    @29
    vl
    cv
    #
    cF
    cfv
    #
    cfv
    #
    cmpt
    #
    @11
    wcel
    #
    vy
    vi
    cZ
    vl
    vi
    cv
    #
    cuz
    cfv
    #
    @38
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
    vw
    cv
    #
    @3
    cfv
    #
    cmpt
    #
    @11
    wcel
    #
    vw
    vi
    cZ
    vm
    @43
    @4
    ciin
    #
    ciun
    #
    crab
    #
    cD
    @13
    @31
    @11
    wcel
    #
    vy
    @6
    crab
    @47
    smflim.d
    @12
    @55
    vx
    vy
    @6
    @16
    vy
    @6
    nfcv
    @12
    vy
    nfv
    vx
    @31
    @11
    vx
    vm
    cZ
    @30
    @14
    vx
    @29
    @3
    @15
    vx
    @29
    nfcv
    #
    nffv
    nfmpt
    #
    nfel1
    @8
    @29
    wceq
    #
    @10
    @31
    @11
    @58
    vm
    cZ
    @9
    @30
    @8
    @29
    @3
    fveq2
    mpteq2dv
    #
    eleq1d
    cbvrab
    @55
    @41
    vy
    @6
    @46
    @29
    @6
    wcel
    @29
    @46
    wcel
    @55
    @41
    @6
    @46
    @29
    vn
    vi
    cZ
    @5
    @45
    @0
    @42
    wceq
    #
    @5
    vl
    @1
    @44
    ciin
    #
    @45
    @5
    @61
    wceq
    @60
    vm
    vl
    @1
    @4
    @44
    vl
    @4
    nfcv
    #
    vm
    @38
    vm
    @37
    cF
    smflim.n
    vm
    @37
    nfcv
    nffv
    #
    nfdm
    #
    @2
    @37
    wceq
    #
    @3
    @38
    @2
    @37
    cF
    fveq2
    #
    dmeqd
    cbviin
    a1i
    @60
    vl
    @1
    @43
    @44
    @44
    @0
    @42
    cuz
    fveq2
    @60
    @37
    @43
    wcel
    wa
    @44
    eqidd
    iineq12dv
    eqtrd
    cbviunv
    eleq2i
    @31
    @40
    @11
    vm
    vl
    cZ
    @30
    @39
    @35
    vl
    cZ
    nfcv
    #
    vl
    @30
    nfcv
    vm
    @29
    @38
    @63
    @34
    nffv
    #
    @65
    @29
    @3
    @38
    @66
    fveq1d
    cbvmptf
    eleq1i
    anbi12i
    rabbia2
    3eqtri
    #
    @47
    vl
    cZ
    @48
    @38
    cfv
    #
    cmpt
    #
    @11
    wcel
    #
    vw
    @46
    crab
    @54
    @41
    @72
    vy
    vw
    @46
    @29
    @48
    wceq
    #
    @40
    @71
    @11
    @73
    vl
    cZ
    @39
    @70
    @29
    @48
    @38
    fveq2
    mpteq2dv
    eleq1d
    cbvrabv
    @72
    @51
    vw
    @46
    @53
    @48
    @46
    wcel
    @48
    @53
    wcel
    @72
    @51
    @46
    @53
    @48
    vi
    cZ
    @45
    @52
    @45
    @52
    wceq
    @42
    cZ
    wcel
    vl
    vm
    @43
    @44
    @4
    @64
    @62
    @37
    @2
    wceq
    #
    @38
    @3
    @37
    @2
    cF
    fveq2
    #
    dmeqd
    #
    cbviin
    a1i
    iuneq2i
    eleq2i
    @71
    @50
    @11
    vl
    vm
    cZ
    @70
    @49
    @67
    @35
    vm
    @48
    @38
    @63
    vm
    @48
    nfcv
    nffv
    vl
    @49
    nfcv
    @74
    @48
    @38
    @3
    @75
    fveq1d
    cbvmptf
    eleq1i
    anbi12i
    rabbia2
    eqtri
    eqtri
    wph
    @33
    simpr
    fnlimfvre
    cG
    vx
    cD
    @10
    cli
    cfv
    #
    cmpt
    #
    vy
    cD
    @32
    cmpt
    smflim.g
    vx
    vy
    cD
    @77
    @32
    vx
    cD
    @13
    smflim.d
    @12
    vx
    @6
    nfrab1
    nfcxfr
    #
    vy
    cD
    nfcv
    #
    vy
    @77
    nfcv
    #
    vx
    @31
    cli
    vx
    cli
    nfcv
    #
    @57
    nffv
    @58
    @10
    @31
    cli
    @59
    fveq2d
    cbvmptf
    eqtri
    fmptd
    wph
    va
    cv
    #
    cr
    wcel
    #
    wa
    vy
    @83
    cD
    vm
    vk
    cZ
    cn
    @9
    @83
    c1
    vk
    cv
    #
    cdiv
    co
    #
    caddc
    co
    #
    clt
    wbr
    #
    vx
    @4
    crab
    #
    vs
    cv
    #
    @4
    cin
    #
    wceq
    #
    vs
    cS
    crab
    #
    cmpt2
    #
    cS
    vj
    vl
    vi
    cF
    cG
    cM
    cZ
    vt
    wph
    cM
    cz
    wcel
    @84
    smflim.m
    adantr
    smflim.z
    wph
    @26
    @84
    smflim.s
    adantr
    wph
    cZ
    @27
    cF
    wf
    @84
    smflim.f
    adantr
    @69
    cG
    @78
    vy
    cD
    @40
    cli
    cfv
    #
    cmpt
    smflim.g
    vx
    vy
    cD
    @77
    @95
    @79
    @80
    @81
    vx
    @40
    cli
    @82
    vx
    vl
    cZ
    @39
    @14
    vx
    @29
    @38
    vx
    @37
    cF
    smflim.x
    vx
    @37
    nfcv
    nffv
    #
    @56
    nffv
    #
    nfmpt
    nffv
    @58
    @10
    @40
    cli
    @58
    @10
    vl
    cZ
    @8
    @38
    cfv
    #
    cmpt
    #
    @40
    @10
    @99
    wceq
    @58
    vm
    vl
    cZ
    @9
    @98
    @35
    @67
    vl
    @9
    nfcv
    vm
    @8
    @38
    @63
    vm
    @8
    nfcv
    nffv
    @65
    @8
    @3
    @38
    @66
    fveq1d
    cbvmptf
    a1i
    @58
    vl
    cZ
    @98
    @39
    @58
    @37
    cZ
    wcel
    #
    wa
    @8
    @29
    @38
    @58
    @100
    simpl
    fveq2d
    mpteq2dva
    eqtrd
    fveq2d
    cbvmptf
    eqtri
    wph
    @84
    simpr
    vl
    vj
    cZ
    cn
    @39
    @83
    c1
    vj
    cv
    #
    cdiv
    co
    #
    caddc
    co
    #
    clt
    wbr
    #
    vy
    @44
    crab
    #
    vt
    cv
    #
    @44
    cin
    #
    wceq
    #
    vt
    cS
    crab
    #
    cmpt2
    @94
    vl
    vj
    vm
    vk
    cZ
    cn
    @109
    @93
    @108
    vm
    vt
    cS
    vm
    @105
    @107
    @104
    vm
    vy
    @44
    vm
    @39
    @103
    clt
    @68
    vm
    clt
    nfcv
    vm
    @103
    nfcv
    nfbr
    @64
    nfrab
    vm
    @106
    @44
    vm
    @106
    nfcv
    @64
    nfin
    nfeq
    vm
    cS
    nfcv
    nfrab
    vk
    @109
    nfcv
    vl
    @93
    nfcv
    vj
    @93
    nfcv
    @74
    @101
    @85
    wceq
    #
    @109
    @9
    @103
    clt
    wbr
    #
    vx
    @4
    crab
    #
    @91
    wceq
    #
    vs
    cS
    crab
    #
    @93
    @74
    @109
    @98
    @103
    clt
    wbr
    #
    vx
    @44
    crab
    #
    @90
    @44
    cin
    #
    wceq
    #
    vs
    cS
    crab
    #
    @114
    @109
    @119
    wceq
    @74
    @108
    @118
    vt
    vs
    cS
    @106
    @90
    wceq
    #
    @105
    @116
    @107
    @117
    @105
    @116
    wceq
    @120
    @104
    @115
    vy
    vx
    @44
    vy
    @44
    nfcv
    vx
    @38
    @96
    nfdm
    vx
    @39
    @103
    clt
    @97
    vx
    clt
    nfcv
    vx
    @103
    nfcv
    nfbr
    @115
    vy
    nfv
    @29
    @8
    wceq
    @39
    @98
    @103
    clt
    @29
    @8
    @38
    fveq2
    breq1d
    cbvrab
    a1i
    @106
    @90
    @44
    ineq1
    eqeq12d
    cbvrabv
    a1i
    @74
    @118
    @113
    vs
    cS
    @74
    @116
    @112
    @117
    @91
    @74
    @115
    @111
    vx
    @44
    @4
    @74
    @8
    @44
    wcel
    @8
    @4
    wcel
    @115
    @111
    @74
    @44
    @4
    @8
    @76
    eleq2d
    @74
    @98
    @9
    @103
    clt
    @74
    @8
    @38
    @3
    @75
    fveq1d
    breq1d
    anbi12d
    rabbidva2
    @74
    @44
    @4
    @90
    @76
    ineq2d
    eqeq12d
    rabbidv
    eqtrd
    @110
    @113
    @92
    vs
    cS
    @110
    @112
    @89
    @91
    @110
    @111
    @88
    vx
    @4
    @110
    @103
    @87
    @9
    clt
    @110
    @102
    @86
    @83
    caddc
    @101
    @85
    c1
    cdiv
    oveq2
    oveq2d
    breq2d
    rabbidv
    eqeq1d
    rabbidv
    sylan9eq
    cbvmpt2
    eqcomi
    smflimlem6
    issmfled
end
