include "cv.mm"
include "cfv.mm"
include "ciun.mm"
include "cin.mm"
include "cdif.mm"
include "cxad.mm"
include "co.mm"
include "caddc.mm"
include "cle.mm"
include "cr.mm"
include "wcel.mm"
include "wceq.mm"
include "wss.mm"
include "inss1.mm"
include "a1i.mm"
include "omessre.mm"
include "difssd.mm"
include "rexadd.mm"
include "syl2anc.mm"
include "clt.mm"
include "wbr.mm"
include "wrex.mm"
include "cfz.mm"
include "csu.mm"
include "cpw.mm"
include "cfn.mm"
include "cmpt.mm"
include "wf.mm"
include "ssinss1.mm"
include "syl.mm"
include "cvv.mm"
include "wb.mm"
include "come.mm"
include "unidmex.mm"
include "ssexg.mm"
include "inex1g.mm"
include "elpwg.mm"
include "mpbird.mm"
include "adantr.mm"
include "eqid.mm"
include "fmptd.mm"
include "fveq2.mm"
include "ineq2d.mm"
include "cbvmptv.mm"
include "feq1i.mm"
include "wa.mm"
include "simpr.mm"
include "fvmpt2.mm"
include "iuneq2dv.mm"
include "fveq2d.mm"
include "wral.mm"
include "wdisj.mm"
include "nfv.mm"
include "iundjiun.mm"
include "simplrd.mm"
include "eqcomd.mm"
include "iunin2.mm"
include "eqcomi.mm"
include "eqtrd.mm"
include "eqeltrrd.mm"
include "eqeltrd.mm"
include "omeiunltfirp.mm"
include "elpwinss.mm"
include "sseldd.mm"
include "adantll.mm"
include "ad2antrr.mm"
include "sumeq2dv.mm"
include "oveq1d.mm"
include "breq12d.mm"
include "biimpd.mm"
include "reximdva.mm"
include "mpd.mm"
include "cz.mm"
include "adantl.mm"
include "elinel2.mm"
include "uzfissfz.mm"
include "ad3antrrr.mm"
include "fzfid.mm"
include "id.mm"
include "ssfi.mm"
include "fsumrecl.mm"
include "rpred.mm"
include "readdcld.mm"
include "ad4ant14.mm"
include "simplr.mm"
include "adantlr.mm"
include "cc0.mm"
include "cxr.mm"
include "cpnf.mm"
include "cicc.mm"
include "0xr.mm"
include "pnfxr.mm"
include "omecl.mm"
include "iccgelb.mm"
include "syl3anc.mm"
include "fsumless.mm"
include "leadd1dd.mm"
include "ltletrd.mm"
include "ex.mm"
include "reximdv.mm"
include "rexlimdva.mm"
include "eqbrtrd.mm"
include "carageniuncllem1.mm"
include "breqtrd.mm"
include "w3a.mm"
include "3ad2ant1.mm"
include "3adant3.mm"
include "simp3.mm"
include "ltled.mm"
include "ssdifssd.mm"
include "oveq2.mm"
include "iuneq1d.mm"
include "ovex.mm"
include "fvex.mm"
include "iunex.mm"
include "fvmpt.mm"
include "cbviunv.mm"
include "cuz.mm"
include "elfzuz.mm"
include "eleqtrd.mm"
include "ssriv.mm"
include "iunss1.mm"
include "ax-mp.mm"
include "eqsstrd.mm"
include "sscond.mm"
include "omessle.mm"
include "le2addd.mm"
include "recnd.mm"
include "cc.mm"
include "add32d.mm"
include "ffvelrnd.mm"
include "caragenfiiuncl.mm"
include "fvmptd.mm"
include "caragensplit.mm"
include "3exp.mm"
include "rexlimdv.mm"

theorem carageniuncllem2
  let wph: wff ph
  let cA: class A
  let cS: class S
  let vi: setvar i
  let vn: setvar n
  let cE: class E
  let cF: class F
  let cG: class G
  let cM: class M
  let cO: class O
  let cX: class X
  let cY: class Y
  let cZ: class Z
  let vk: setvar k
  let vz: setvar z
  let vm: setvar m
  let vx: setvar x
  assume carageniuncllem2.o: |- ( ph -> O e. OutMeas )
  assume carageniuncllem2.s: |- S = ( CaraGen ` O )
  assume carageniuncllem2.x: |- X = U. dom O
  assume carageniuncllem2.a: |- ( ph -> A C_ X )
  assume carageniuncllem2.re: |- ( ph -> ( O ` A ) e. RR )
  assume carageniuncllem2.m: |- ( ph -> M e. ZZ )
  assume carageniuncllem2.z: |- Z = ( ZZ>= ` M )
  assume carageniuncllem2.e: |- ( ph -> E : Z --> S )
  assume carageniuncllem2.y: |- ( ph -> Y e. RR+ )
  assume carageniuncllem2.g: |- G = ( n e. Z |-> U_ i e. ( M ... n ) ( E ` i ) )
  assume carageniuncllem2.f: |- F = ( n e. Z |-> ( ( E ` n ) \ U_ i e. ( M ..^ n ) ( E ` i ) ) )

  disjoint A n
  disjoint E i
  disjoint E n
  disjoint i n
  disjoint F n
  disjoint M i
  disjoint M n
  disjoint O n
  disjoint S i
  disjoint X n
  disjoint Z i
  disjoint Z n
  disjoint i ph
  disjoint n ph
  disjoint A k
  disjoint A z
  disjoint k n
  disjoint k z
  disjoint n z
  disjoint E k
  disjoint i k
  disjoint E m
  disjoint i m
  disjoint m n
  disjoint F k
  disjoint F z
  disjoint F m
  disjoint M k
  disjoint M m
  disjoint M z
  disjoint O k
  disjoint O z
  disjoint Y k
  disjoint Y z
  disjoint Z k
  disjoint Z m
  disjoint Z z
  disjoint k ph
  disjoint m ph
  disjoint ph z
  disjoint k x
  assert |- ( ph -> ( ( O ` ( A i^i U_ n e. Z ( E ` n ) ) ) +e ( O ` ( A \ U_ n e. Z ( E ` n ) ) ) ) <_ ( ( O ` A ) + Y ) )

  proof
    wph
    cA
    vn
    cZ
    vn
    cv
    #
    cE
    cfv
    #
    ciun
    #
    cin
    #
    cO
    cfv
    #
    cA
    @2
    cdif
    #
    cO
    cfv
    #
    cxad
    co
    #
    @4
    @6
    caddc
    co
    #
    cA
    cO
    cfv
    #
    cY
    caddc
    co
    #
    cle
    wph
    @4
    cr
    wcel
    #
    @6
    cr
    wcel
    #
    @7
    @8
    wceq
    wph
    cA
    @3
    cO
    cX
    carageniuncllem2.o
    carageniuncllem2.x
    carageniuncllem2.a
    carageniuncllem2.re
    @3
    cA
    wss
    wph
    cA
    @2
    inss1
    a1i
    omessre
    #
    wph
    cA
    @5
    cO
    cX
    carageniuncllem2.o
    carageniuncllem2.x
    carageniuncllem2.a
    carageniuncllem2.re
    wph
    cA
    @2
    difssd
    omessre
    #
    @4
    @6
    rexadd
    syl2anc
    wph
    @4
    cA
    vk
    cv
    #
    cG
    cfv
    #
    cin
    #
    cO
    cfv
    #
    cY
    caddc
    co
    #
    clt
    wbr
    #
    vk
    cZ
    wrex
    #
    @8
    @10
    cle
    wbr
    #
    wph
    @4
    cM
    @15
    cfz
    co
    #
    cA
    @0
    cF
    cfv
    #
    cin
    #
    cO
    cfv
    #
    vn
    csu
    #
    cY
    caddc
    co
    #
    clt
    wbr
    #
    vk
    cZ
    wrex
    #
    @21
    wph
    vn
    cZ
    @25
    ciun
    #
    cO
    cfv
    #
    @28
    clt
    wbr
    #
    vk
    cZ
    wrex
    #
    @30
    wph
    @32
    vz
    cv
    #
    @26
    vn
    csu
    #
    cY
    caddc
    co
    #
    clt
    wbr
    #
    vz
    cZ
    cpw
    #
    cfn
    cin
    #
    wrex
    #
    @34
    wph
    vn
    cZ
    @0
    vk
    cZ
    cA
    @15
    cF
    cfv
    #
    cin
    #
    cmpt
    #
    cfv
    #
    ciun
    #
    cO
    cfv
    #
    @35
    @45
    cO
    cfv
    #
    vn
    csu
    #
    cY
    caddc
    co
    #
    clt
    wbr
    #
    vz
    @40
    wrex
    @41
    wph
    vz
    vn
    @44
    cM
    cO
    cX
    cY
    cZ
    carageniuncllem2.o
    carageniuncllem2.x
    carageniuncllem2.z
    wph
    cZ
    cX
    cpw
    #
    @44
    wf
    #
    cZ
    @52
    vn
    cZ
    @25
    cmpt
    #
    wf
    #
    wph
    vn
    cZ
    @25
    @52
    @54
    wph
    @25
    @52
    wcel
    #
    @0
    cZ
    wcel
    #
    wph
    @56
    @25
    cX
    wss
    #
    wph
    cA
    cX
    wss
    #
    @58
    carageniuncllem2.a
    cA
    @24
    cX
    ssinss1
    syl
    #
    wph
    @25
    cvv
    wcel
    #
    @56
    @58
    wb
    wph
    cA
    cvv
    wcel
    #
    @61
    wph
    @59
    cX
    cvv
    wcel
    @62
    carageniuncllem2.a
    wph
    cO
    come
    cX
    carageniuncllem2.o
    carageniuncllem2.x
    unidmex
    cA
    cX
    cvv
    ssexg
    syl2anc
    cA
    @24
    cvv
    inex1g
    syl
    #
    @25
    cX
    cvv
    elpwg
    syl
    mpbird
    adantr
    @54
    eqid
    fmptd
    @53
    @55
    wb
    wph
    cZ
    @52
    @44
    @54
    vk
    vn
    cZ
    @43
    @25
    @15
    @0
    wceq
    @42
    @24
    cA
    @15
    @0
    cF
    fveq2
    ineq2d
    cbvmptv
    #
    feq1i
    a1i
    mpbird
    wph
    @47
    @32
    cr
    wph
    @46
    @31
    cO
    wph
    vn
    cZ
    @45
    @25
    wph
    @57
    wa
    @57
    @61
    @45
    @25
    wceq
    #
    wph
    @57
    simpr
    wph
    @61
    @57
    @63
    adantr
    vn
    cZ
    @25
    cvv
    @44
    @64
    fvmpt2
    #
    syl2anc
    iuneq2dv
    fveq2d
    #
    wph
    @4
    @32
    cr
    wph
    @3
    @31
    cO
    wph
    @3
    cA
    vn
    cZ
    @24
    ciun
    #
    cin
    #
    @31
    wph
    @2
    @68
    cA
    wph
    @68
    @2
    wph
    vn
    cM
    vm
    cv
    cfz
    co
    #
    @24
    ciun
    vn
    @70
    @1
    ciun
    wceq
    vm
    cZ
    wral
    @68
    @2
    wceq
    vn
    cZ
    @24
    wdisj
    wph
    vi
    vm
    vn
    cE
    cF
    cM
    cS
    cZ
    wph
    vn
    nfv
    carageniuncllem2.z
    carageniuncllem2.e
    carageniuncllem2.f
    iundjiun
    simplrd
    eqcomd
    ineq2d
    @69
    @31
    wceq
    wph
    @31
    @69
    vn
    cZ
    cA
    @24
    iunin2
    eqcomi
    a1i
    eqtrd
    fveq2d
    #
    @13
    eqeltrrd
    #
    eqeltrd
    carageniuncllem2.y
    omeiunltfirp
    wph
    @51
    @38
    vz
    @40
    wph
    @35
    @40
    wcel
    #
    wa
    #
    @51
    @38
    @74
    @47
    @32
    @50
    @37
    clt
    wph
    @47
    @32
    wceq
    @73
    @67
    adantr
    @74
    @49
    @36
    cY
    caddc
    @74
    @35
    @48
    @26
    vn
    @74
    @0
    @35
    wcel
    #
    wa
    #
    @45
    @25
    cO
    @76
    @57
    @61
    @65
    @73
    @75
    @57
    wph
    @73
    @75
    wa
    @35
    cZ
    @0
    @73
    @35
    cZ
    wss
    #
    @75
    @35
    cZ
    cfn
    elpwinss
    #
    adantr
    @73
    @75
    simpr
    sseldd
    adantll
    wph
    @61
    @73
    @75
    @63
    ad2antrr
    @66
    syl2anc
    fveq2d
    sumeq2dv
    oveq1d
    breq12d
    biimpd
    reximdva
    mpd
    wph
    @38
    @34
    vz
    @40
    @74
    @38
    @34
    @74
    @38
    wa
    #
    @35
    @23
    wss
    #
    vk
    cZ
    wrex
    #
    @34
    @74
    @81
    @38
    @74
    @35
    vk
    cM
    cZ
    wph
    cM
    cz
    wcel
    @73
    carageniuncllem2.m
    adantr
    carageniuncllem2.z
    @73
    @77
    wph
    @78
    adantl
    @73
    @35
    cfn
    wcel
    #
    wph
    @35
    @39
    cfn
    elinel2
    adantl
    uzfissfz
    adantr
    @79
    @80
    @33
    vk
    cZ
    @79
    @80
    @33
    @79
    @80
    wa
    @32
    @37
    @28
    wph
    @32
    cr
    wcel
    @73
    @38
    @80
    @72
    ad3antrrr
    wph
    @80
    @37
    cr
    wcel
    @73
    @38
    wph
    @80
    wa
    #
    @36
    cY
    @83
    @35
    @26
    vn
    @80
    @82
    wph
    @80
    @23
    cfn
    wcel
    @80
    @82
    @80
    cM
    @15
    fzfid
    @80
    id
    @23
    @35
    ssfi
    syl2anc
    adantl
    @83
    @75
    wa
    #
    cA
    @25
    cO
    cX
    wph
    cO
    come
    wcel
    #
    @80
    @75
    carageniuncllem2.o
    ad2antrr
    carageniuncllem2.x
    wph
    @59
    @80
    @75
    carageniuncllem2.a
    ad2antrr
    wph
    @9
    cr
    wcel
    #
    @80
    @75
    carageniuncllem2.re
    ad2antrr
    @25
    cA
    wss
    #
    @84
    cA
    @24
    inss1
    #
    a1i
    omessre
    fsumrecl
    #
    wph
    cY
    cr
    wcel
    #
    @80
    wph
    cY
    carageniuncllem2.y
    rpred
    #
    adantr
    #
    readdcld
    ad4ant14
    @74
    @28
    cr
    wcel
    @38
    @80
    @74
    @27
    cY
    wph
    @27
    cr
    wcel
    #
    @73
    wph
    @23
    @26
    vn
    wph
    cM
    @15
    fzfid
    #
    wph
    @26
    cr
    wcel
    #
    @0
    @23
    wcel
    #
    wph
    cA
    @25
    cO
    cX
    carageniuncllem2.o
    carageniuncllem2.x
    carageniuncllem2.a
    carageniuncllem2.re
    @87
    wph
    @88
    a1i
    omessre
    adantr
    #
    fsumrecl
    #
    adantr
    wph
    @90
    @73
    @91
    adantr
    readdcld
    ad2antrr
    @74
    @38
    @80
    simplr
    wph
    @80
    @37
    @28
    cle
    wbr
    @73
    @38
    @83
    @36
    @27
    cY
    @89
    wph
    @93
    @80
    @98
    adantr
    @92
    @83
    @23
    @26
    @35
    vn
    @83
    cM
    @15
    fzfid
    wph
    @96
    @95
    @80
    @97
    adantlr
    wph
    @96
    cc0
    @26
    cle
    wbr
    #
    @80
    wph
    @96
    wa
    #
    cc0
    cxr
    wcel
    #
    cpnf
    cxr
    wcel
    #
    @26
    cc0
    cpnf
    cicc
    co
    wcel
    #
    @99
    @101
    @100
    0xr
    a1i
    @102
    @100
    pnfxr
    a1i
    wph
    @103
    @96
    wph
    @25
    cO
    cX
    carageniuncllem2.o
    carageniuncllem2.x
    @60
    omecl
    adantr
    cc0
    cpnf
    @26
    iccgelb
    syl3anc
    adantlr
    wph
    @80
    simpr
    fsumless
    leadd1dd
    ad4ant14
    ltletrd
    ex
    reximdv
    mpd
    ex
    rexlimdva
    mpd
    wph
    @33
    @29
    vk
    cZ
    wph
    @15
    cZ
    wcel
    #
    wa
    #
    @33
    @29
    @105
    @33
    wa
    @4
    @32
    @28
    clt
    wph
    @4
    @32
    wceq
    @104
    @33
    @71
    ad2antrr
    @105
    @33
    simpr
    eqbrtrd
    ex
    reximdva
    mpd
    wph
    @29
    @20
    vk
    cZ
    @105
    @29
    @20
    @105
    @29
    wa
    @4
    @28
    @19
    clt
    @105
    @29
    simpr
    @105
    @28
    @19
    wceq
    @29
    @105
    @27
    @18
    cY
    caddc
    @105
    cA
    cS
    vi
    vn
    cE
    cF
    cG
    @15
    cM
    cO
    cX
    cZ
    wph
    @85
    @104
    carageniuncllem2.o
    adantr
    #
    carageniuncllem2.s
    carageniuncllem2.x
    wph
    @59
    @104
    carageniuncllem2.a
    adantr
    #
    wph
    @86
    @104
    carageniuncllem2.re
    adantr
    #
    carageniuncllem2.z
    wph
    cZ
    cS
    cE
    wf
    #
    @104
    carageniuncllem2.e
    adantr
    carageniuncllem2.g
    carageniuncllem2.f
    wph
    @104
    simpr
    #
    carageniuncllem1
    oveq1d
    adantr
    breqtrd
    ex
    reximdva
    mpd
    wph
    @20
    @22
    vk
    cZ
    wph
    @104
    @20
    @22
    wph
    @104
    @20
    w3a
    #
    @8
    @19
    cA
    @16
    cdif
    #
    cO
    cfv
    #
    caddc
    co
    #
    @10
    cle
    @111
    @4
    @6
    @19
    @113
    wph
    @104
    @11
    @20
    @13
    3ad2ant1
    #
    wph
    @104
    @12
    @20
    @14
    3ad2ant1
    wph
    @104
    @19
    cr
    wcel
    @20
    @105
    @18
    cY
    @105
    cA
    @17
    cO
    cX
    @106
    carageniuncllem2.x
    @107
    @108
    @17
    cA
    wss
    @105
    cA
    @16
    inss1
    a1i
    omessre
    #
    wph
    @90
    @104
    @91
    adantr
    readdcld
    3adant3
    #
    wph
    @104
    @113
    cr
    wcel
    #
    @20
    @105
    cA
    @112
    cO
    cX
    @106
    carageniuncllem2.x
    @107
    @108
    @105
    cA
    @16
    difssd
    omessre
    #
    3adant3
    @111
    @4
    @19
    @115
    @117
    wph
    @104
    @20
    simp3
    ltled
    wph
    @104
    @6
    @113
    cle
    wbr
    @20
    @105
    @5
    @112
    cO
    cX
    @106
    carageniuncllem2.x
    @105
    cA
    cX
    @16
    @107
    ssdifssd
    @105
    @16
    @2
    cA
    @104
    @16
    @2
    wss
    wph
    @104
    @16
    vn
    @23
    @1
    ciun
    #
    @2
    @104
    @16
    vi
    @23
    vi
    cv
    #
    cE
    cfv
    #
    ciun
    #
    @120
    vn
    @15
    vi
    cM
    @0
    cfz
    co
    #
    @122
    ciun
    #
    @123
    cZ
    cG
    @0
    @15
    wceq
    #
    vi
    @124
    @23
    @122
    @0
    @15
    cM
    cfz
    oveq2
    iuneq1d
    #
    carageniuncllem2.g
    vi
    @23
    @122
    cM
    @15
    cfz
    ovex
    @121
    cE
    fvex
    iunex
    fvmpt
    @123
    @120
    wceq
    @104
    vi
    vn
    @23
    @122
    @1
    @121
    @0
    cE
    fveq2
    cbviunv
    a1i
    eqtrd
    @120
    @2
    wss
    #
    @104
    @23
    cZ
    wss
    @128
    vi
    @23
    cZ
    @121
    @23
    wcel
    #
    @121
    cM
    cuz
    cfv
    #
    cZ
    @121
    cM
    @15
    elfzuz
    @130
    cZ
    wceq
    @129
    cZ
    @130
    carageniuncllem2.z
    eqcomi
    a1i
    eleqtrd
    #
    ssriv
    vn
    @23
    cZ
    @1
    iunss1
    ax-mp
    a1i
    eqsstrd
    adantl
    sscond
    omessle
    3adant3
    le2addd
    wph
    @104
    @114
    @10
    wceq
    @20
    @105
    @114
    @18
    @113
    caddc
    co
    #
    cY
    caddc
    co
    @10
    @105
    @18
    cY
    @113
    @105
    @18
    @116
    recnd
    wph
    cY
    cc
    wcel
    @104
    wph
    cY
    @91
    recnd
    adantr
    @105
    @113
    @119
    recnd
    add32d
    @105
    @132
    @9
    cY
    caddc
    @105
    @132
    @18
    @113
    cxad
    co
    #
    @9
    @105
    @133
    @132
    @105
    @18
    cr
    wcel
    @118
    @133
    @132
    wceq
    @116
    @119
    @18
    @113
    rexadd
    syl2anc
    eqcomd
    @105
    cA
    cS
    @16
    cO
    cX
    @106
    carageniuncllem2.s
    carageniuncllem2.x
    @105
    @16
    @123
    cS
    @105
    vn
    @15
    @125
    @123
    cZ
    cG
    cS
    cG
    vn
    cZ
    @125
    cmpt
    wceq
    @105
    carageniuncllem2.g
    a1i
    @126
    @125
    @123
    wceq
    @105
    @127
    adantl
    @110
    wph
    @123
    cS
    wcel
    @104
    wph
    @23
    @122
    cS
    vi
    cO
    wph
    vi
    nfv
    carageniuncllem2.o
    carageniuncllem2.s
    @94
    wph
    @129
    wa
    cZ
    cS
    @121
    cE
    wph
    @109
    @129
    carageniuncllem2.e
    adantr
    @129
    @121
    cZ
    wcel
    wph
    @131
    adantl
    ffvelrnd
    caragenfiiuncl
    adantr
    #
    fvmptd
    @134
    eqeltrd
    @107
    caragensplit
    eqtrd
    oveq1d
    eqtrd
    3adant3
    breqtrd
    3exp
    rexlimdv
    mpd
    eqbrtrd
end
