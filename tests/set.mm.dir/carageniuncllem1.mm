include "cfz.mm"
include "co.mm"
include "wcel.mm"
include "cv.mm"
include "cfv.mm"
include "cin.mm"
include "csu.mm"
include "wceq.mm"
include "cuz.mm"
include "syl6eleq.mm"
include "eluzfz2.mm"
include "syl.mm"
include "id.mm"
include "wi.mm"
include "c1.mm"
include "caddc.mm"
include "oveq2.mm"
include "sumeq1d.mm"
include "fveq2.mm"
include "ineq2d.mm"
include "fveq2d.mm"
include "eqeq12d.mm"
include "imbi2d.mm"
include "csn.mm"
include "cz.mm"
include "eluzel2.mm"
include "fzsn.mm"
include "cc.mm"
include "wss.mm"
include "inss1.mm"
include "a1i.mm"
include "omessre.mm"
include "recnd.mm"
include "sumsn.mm"
include "syl2anc.mm"
include "eqidd.mm"
include "cfzo.mm"
include "ciun.mm"
include "cdif.mm"
include "c0.mm"
include "cvv.mm"
include "cmpt.mm"
include "iuneq1d.mm"
include "difeq12d.mm"
include "adantl.mm"
include "uzid.mm"
include "eqcomd.mm"
include "eleqtrd.mm"
include "fvex.mm"
include "difexg.mm"
include "ax-mp.mm"
include "fvmptd.mm"
include "fzo0.mm"
include "iuneq1.mm"
include "0iun.mm"
include "eqtri.mm"
include "difeq2i.mm"
include "dif0.mm"
include "3eqtrd.mm"
include "ovex.mm"
include "iunex.mm"
include "iunxsng.mm"
include "3eqtr4d.mm"
include "w3a.mm"
include "simp3.mm"
include "simp1.mm"
include "imp.mm"
include "3adant1.mm"
include "wa.mm"
include "elfzouz.mm"
include "come.mm"
include "adantr.mm"
include "cr.mm"
include "adantlr.mm"
include "fsump1.mm"
include "3adant3.mm"
include "oveq1.mm"
include "3ad2ant3.mm"
include "cxad.mm"
include "fzssp1.mm"
include "iunss1.mm"
include "syl6eleqr.mm"
include "peano2uz.mm"
include "eqcomi.mm"
include "sseq12d.mm"
include "mpbird.mm"
include "inabs3.mm"
include "elfzoelz.mm"
include "fzval3.mm"
include "difeq2d.mm"
include "cun.mm"
include "nfcv.mm"
include "iunp1.mm"
include "eqtrd.mm"
include "difundir.mm"
include "difid.mm"
include "uneq1i.mm"
include "0un.mm"
include "3eqtri.mm"
include "indif2.mm"
include "eqtr4d.mm"
include "oveq12d.mm"
include "sstri.mm"
include "difss.mm"
include "rexadd.mm"
include "nfv.mm"
include "fzfid.mm"
include "wf.mm"
include "elfzuz.mm"
include "ffvelrnd.mm"
include "caragenfiiuncl.mm"
include "eqeltrd.mm"
include "ssinss1d.mm"
include "caragensplit.mm"
include "syl3anc.mm"
include "3exp.mm"
include "fzind2.mm"
include "sylc.mm"

theorem carageniuncllem1
  let wph: wff ph
  let cA: class A
  let cS: class S
  let vi: setvar i
  let vn: setvar n
  let cE: class E
  let cF: class F
  let cG: class G
  let cK: class K
  let cM: class M
  let cO: class O
  let cX: class X
  let cZ: class Z
  let vj: setvar j
  let vk: setvar k
  let vx: setvar x
  assume carageniuncllem1.o: |- ( ph -> O e. OutMeas )
  assume carageniuncllem1.s: |- S = ( CaraGen ` O )
  assume carageniuncllem1.x: |- X = U. dom O
  assume carageniuncllem1.a: |- ( ph -> A C_ X )
  assume carageniuncllem1.re: |- ( ph -> ( O ` A ) e. RR )
  assume carageniuncllem1.z: |- Z = ( ZZ>= ` M )
  assume carageniuncllem1.e: |- ( ph -> E : Z --> S )
  assume carageniuncllem1.g: |- G = ( n e. Z |-> U_ i e. ( M ... n ) ( E ` i ) )
  assume carageniuncllem1.f: |- F = ( n e. Z |-> ( ( E ` n ) \ U_ i e. ( M ..^ n ) ( E ` i ) ) )
  assume carageniuncllem1.k: |- ( ph -> K e. Z )

  disjoint A n
  disjoint E i
  disjoint E n
  disjoint i n
  disjoint F n
  disjoint K n
  disjoint M i
  disjoint M n
  disjoint O n
  disjoint S i
  disjoint Z n
  disjoint i ph
  disjoint n ph
  disjoint A j
  disjoint A k
  disjoint j k
  disjoint j n
  disjoint k n
  disjoint F j
  disjoint F k
  disjoint G j
  disjoint G k
  disjoint K j
  disjoint K k
  disjoint M j
  disjoint i j
  disjoint M k
  disjoint O j
  disjoint O k
  disjoint j ph
  disjoint k ph
  disjoint k x
  assert |- ( ph -> sum_ n e. ( M ... K ) ( O ` ( A i^i ( F ` n ) ) ) = ( O ` ( A i^i ( G ` K ) ) ) )

  proof
    wph
    cK
    cM
    cK
    cfz
    co
    #
    wcel
    #
    wph
    @0
    cA
    vn
    cv
    #
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
    cA
    cK
    cG
    cfv
    #
    cin
    #
    cO
    cfv
    #
    wceq
    #
    wph
    cK
    cM
    cuz
    cfv
    #
    wcel
    #
    @1
    wph
    cK
    cZ
    @11
    carageniuncllem1.k
    carageniuncllem1.z
    syl6eleq
    #
    cM
    cK
    eluzfz2
    syl
    wph
    id
    wph
    cM
    vk
    cv
    #
    cfz
    co
    #
    @5
    vn
    csu
    #
    cA
    @14
    cG
    cfv
    #
    cin
    #
    cO
    cfv
    #
    wceq
    #
    wi
    wph
    cM
    cM
    cfz
    co
    #
    @5
    vn
    csu
    #
    cA
    cM
    cG
    cfv
    #
    cin
    #
    cO
    cfv
    #
    wceq
    #
    wi
    #
    wph
    cM
    vj
    cv
    #
    cfz
    co
    #
    @5
    vn
    csu
    #
    cA
    @28
    cG
    cfv
    #
    cin
    #
    cO
    cfv
    #
    wceq
    #
    wi
    #
    wph
    cM
    @28
    c1
    caddc
    co
    #
    cfz
    co
    #
    @5
    vn
    csu
    #
    cA
    @36
    cG
    cfv
    #
    cin
    #
    cO
    cfv
    #
    wceq
    #
    wi
    wph
    @10
    wi
    vk
    vj
    cK
    cM
    cK
    @14
    cM
    wceq
    #
    @20
    @26
    wph
    @43
    @16
    @22
    @19
    @25
    @43
    @15
    @21
    @5
    vn
    @14
    cM
    cM
    cfz
    oveq2
    sumeq1d
    @43
    @18
    @24
    cO
    @43
    @17
    @23
    cA
    @14
    cM
    cG
    fveq2
    ineq2d
    fveq2d
    eqeq12d
    imbi2d
    @14
    @28
    wceq
    #
    @20
    @34
    wph
    @44
    @16
    @30
    @19
    @33
    @44
    @15
    @29
    @5
    vn
    @14
    @28
    cM
    cfz
    oveq2
    sumeq1d
    @44
    @18
    @32
    cO
    @44
    @17
    @31
    cA
    @14
    @28
    cG
    fveq2
    ineq2d
    fveq2d
    eqeq12d
    imbi2d
    @14
    @36
    wceq
    #
    @20
    @42
    wph
    @45
    @16
    @38
    @19
    @41
    @45
    @15
    @37
    @5
    vn
    @14
    @36
    cM
    cfz
    oveq2
    sumeq1d
    @45
    @18
    @40
    cO
    @45
    @17
    @39
    cA
    @14
    @36
    cG
    fveq2
    ineq2d
    fveq2d
    eqeq12d
    imbi2d
    @14
    cK
    wceq
    #
    @20
    @10
    wph
    @46
    @16
    @6
    @19
    @9
    @46
    @15
    @0
    @5
    vn
    @14
    cK
    cM
    cfz
    oveq2
    sumeq1d
    @46
    @18
    @8
    cO
    @46
    @17
    @7
    cA
    @14
    cK
    cG
    fveq2
    ineq2d
    fveq2d
    eqeq12d
    imbi2d
    @27
    @12
    wph
    @22
    cM
    csn
    #
    @5
    vn
    csu
    #
    cA
    cM
    cF
    cfv
    #
    cin
    #
    cO
    cfv
    #
    @25
    wph
    @21
    @47
    @5
    vn
    wph
    cM
    cz
    wcel
    #
    @21
    @47
    wceq
    wph
    @12
    @52
    @13
    cM
    cK
    eluzel2
    syl
    #
    cM
    fzsn
    syl
    #
    sumeq1d
    wph
    @52
    @51
    cc
    wcel
    @48
    @51
    wceq
    @53
    wph
    @51
    wph
    cA
    @50
    cO
    cX
    carageniuncllem1.o
    carageniuncllem1.x
    carageniuncllem1.a
    carageniuncllem1.re
    @50
    cA
    wss
    wph
    cA
    @49
    inss1
    a1i
    omessre
    recnd
    @5
    @51
    vn
    cM
    cz
    @2
    cM
    wceq
    #
    @4
    @50
    cO
    @55
    @3
    @49
    cA
    @2
    cM
    cF
    fveq2
    ineq2d
    fveq2d
    sumsn
    syl2anc
    wph
    cA
    cM
    cE
    cfv
    #
    cin
    #
    cO
    cfv
    #
    @58
    @51
    @25
    wph
    @58
    eqidd
    wph
    @50
    @57
    cO
    wph
    @49
    @56
    cA
    wph
    @49
    @56
    vi
    cM
    cM
    cfzo
    co
    #
    vi
    cv
    #
    cE
    cfv
    #
    ciun
    #
    cdif
    #
    @56
    c0
    cdif
    #
    @56
    wph
    vn
    cM
    @2
    cE
    cfv
    #
    vi
    cM
    @2
    cfzo
    co
    #
    @61
    ciun
    #
    cdif
    #
    @63
    cZ
    cF
    cvv
    cF
    vn
    cZ
    @68
    cmpt
    wceq
    #
    wph
    carageniuncllem1.f
    a1i
    @55
    @68
    @63
    wceq
    wph
    @55
    @65
    @56
    @67
    @62
    @2
    cM
    cE
    fveq2
    @55
    vi
    @66
    @59
    @61
    @2
    cM
    cM
    cfzo
    oveq2
    iuneq1d
    difeq12d
    adantl
    wph
    cM
    @11
    cZ
    wph
    @52
    cM
    @11
    wcel
    @53
    cM
    uzid
    syl
    wph
    cZ
    @11
    cZ
    @11
    wceq
    wph
    carageniuncllem1.z
    a1i
    eqcomd
    eleqtrd
    #
    @63
    cvv
    wcel
    #
    wph
    @56
    cvv
    wcel
    @71
    cM
    cE
    fvex
    @56
    @62
    cvv
    difexg
    ax-mp
    a1i
    fvmptd
    @63
    @64
    wceq
    wph
    @62
    c0
    @56
    @62
    vi
    c0
    @61
    ciun
    #
    c0
    @59
    c0
    wceq
    @62
    @72
    wceq
    cM
    fzo0
    vi
    @59
    c0
    @61
    iuneq1
    ax-mp
    vi
    @61
    0iun
    eqtri
    difeq2i
    a1i
    @64
    @56
    wceq
    wph
    @56
    dif0
    a1i
    3eqtrd
    ineq2d
    fveq2d
    wph
    @24
    @57
    cO
    wph
    @23
    @56
    cA
    wph
    @23
    vi
    @21
    @61
    ciun
    #
    vi
    @47
    @61
    ciun
    #
    @56
    wph
    vn
    cM
    vi
    cM
    @2
    cfz
    co
    #
    @61
    ciun
    #
    @73
    cZ
    cG
    cvv
    cG
    vn
    cZ
    @76
    cmpt
    wceq
    #
    wph
    carageniuncllem1.g
    a1i
    @55
    @76
    @73
    wceq
    wph
    @55
    vi
    @75
    @21
    @61
    @2
    cM
    cM
    cfz
    oveq2
    iuneq1d
    adantl
    @70
    @73
    cvv
    wcel
    wph
    vi
    @21
    @61
    cM
    cM
    cfz
    ovex
    @60
    cE
    fvex
    #
    iunex
    a1i
    fvmptd
    wph
    vi
    @21
    @47
    @61
    @54
    iuneq1d
    wph
    @52
    @74
    @56
    wceq
    @53
    vi
    cM
    @61
    @56
    cz
    @60
    cM
    cE
    fveq2
    iunxsng
    syl
    3eqtrd
    ineq2d
    fveq2d
    3eqtr4d
    3eqtrd
    a1i
    @28
    cM
    cK
    cfzo
    co
    wcel
    #
    @35
    wph
    @42
    @79
    @35
    wph
    w3a
    wph
    @79
    @34
    @42
    @79
    @35
    wph
    simp3
    @79
    @35
    wph
    simp1
    @35
    wph
    @34
    @79
    @35
    wph
    @34
    @35
    id
    imp
    3adant1
    wph
    @79
    @34
    w3a
    @38
    @30
    cA
    @36
    cF
    cfv
    #
    cin
    #
    cO
    cfv
    #
    caddc
    co
    #
    @33
    @82
    caddc
    co
    #
    @41
    wph
    @79
    @38
    @83
    wceq
    @34
    wph
    @79
    wa
    #
    @5
    @82
    vn
    cM
    @28
    @79
    @28
    @11
    wcel
    #
    wph
    @28
    cM
    cK
    elfzouz
    #
    adantl
    wph
    @2
    @37
    wcel
    #
    @5
    cc
    wcel
    @79
    wph
    @88
    wa
    #
    @5
    @89
    cA
    @4
    cO
    cX
    wph
    cO
    come
    wcel
    #
    @88
    carageniuncllem1.o
    adantr
    carageniuncllem1.x
    wph
    cA
    cX
    wss
    #
    @88
    carageniuncllem1.a
    adantr
    wph
    cA
    cO
    cfv
    cr
    wcel
    #
    @88
    carageniuncllem1.re
    adantr
    @4
    cA
    wss
    @89
    cA
    @3
    inss1
    a1i
    omessre
    recnd
    adantlr
    @2
    @36
    wceq
    #
    @4
    @81
    cO
    @93
    @3
    @80
    cA
    @2
    @36
    cF
    fveq2
    ineq2d
    fveq2d
    fsump1
    3adant3
    @34
    wph
    @83
    @84
    wceq
    @79
    @30
    @33
    @82
    caddc
    oveq1
    3ad2ant3
    wph
    @79
    @84
    @41
    wceq
    @34
    @85
    @84
    @40
    @31
    cin
    #
    cO
    cfv
    #
    @40
    @31
    cdif
    #
    cO
    cfv
    #
    caddc
    co
    #
    @95
    @97
    cxad
    co
    #
    @41
    @85
    @33
    @95
    @82
    @97
    caddc
    @79
    @33
    @95
    wceq
    wph
    @79
    @95
    @33
    @79
    @94
    @32
    cO
    @79
    @31
    @39
    wss
    #
    @94
    @32
    wceq
    @79
    @100
    vi
    @29
    @61
    ciun
    #
    vi
    @37
    @61
    ciun
    #
    wss
    #
    @103
    @79
    @29
    @37
    wss
    @103
    cM
    @28
    fzssp1
    vi
    @29
    @37
    @61
    iunss1
    ax-mp
    a1i
    @79
    @31
    @101
    @39
    @102
    @79
    vn
    @28
    @76
    @101
    cZ
    cG
    cvv
    @77
    @79
    carageniuncllem1.g
    a1i
    #
    @2
    @28
    wceq
    #
    @76
    @101
    wceq
    @79
    @105
    vi
    @75
    @29
    @61
    @2
    @28
    cM
    cfz
    oveq2
    iuneq1d
    adantl
    @79
    @28
    @11
    cZ
    @87
    carageniuncllem1.z
    syl6eleqr
    @101
    cvv
    wcel
    @79
    vi
    @29
    @61
    cM
    @28
    cfz
    ovex
    @78
    iunex
    a1i
    fvmptd
    #
    @79
    vn
    @36
    @76
    @102
    cZ
    cG
    cvv
    @104
    @93
    @76
    @102
    wceq
    @79
    @93
    vi
    @75
    @37
    @61
    @2
    @36
    cM
    cfz
    oveq2
    iuneq1d
    adantl
    @79
    @36
    @11
    cZ
    @79
    @86
    @36
    @11
    wcel
    @87
    cM
    @28
    peano2uz
    syl
    cZ
    @11
    carageniuncllem1.z
    eqcomi
    #
    syl6eleq
    #
    @102
    cvv
    wcel
    @79
    vi
    @37
    @61
    cM
    @36
    cfz
    ovex
    @78
    iunex
    a1i
    fvmptd
    #
    sseq12d
    mpbird
    cA
    @39
    @31
    inabs3
    syl
    fveq2d
    eqcomd
    adantl
    @85
    @81
    @96
    cO
    @85
    @81
    cA
    @39
    @31
    cdif
    #
    cin
    #
    @96
    @85
    @80
    @110
    cA
    @85
    @36
    cE
    cfv
    #
    vi
    cM
    @36
    cfzo
    co
    #
    @61
    ciun
    #
    cdif
    #
    @112
    @101
    cdif
    #
    @80
    @110
    @79
    @115
    @116
    wceq
    wph
    @79
    @114
    @101
    @112
    @79
    vi
    @113
    @29
    @61
    @79
    @29
    @113
    @79
    @28
    cz
    wcel
    @29
    @113
    wceq
    @28
    cM
    cK
    elfzoelz
    cM
    @28
    fzval3
    syl
    eqcomd
    iuneq1d
    difeq2d
    adantl
    @79
    @80
    @115
    wceq
    wph
    @79
    vn
    @36
    @68
    @115
    cZ
    cF
    cvv
    @69
    @79
    carageniuncllem1.f
    a1i
    @93
    @68
    @115
    wceq
    @79
    @93
    @65
    @112
    @67
    @114
    @2
    @36
    cE
    fveq2
    @93
    vi
    @66
    @113
    @61
    @2
    @36
    cM
    cfzo
    oveq2
    iuneq1d
    difeq12d
    adantl
    @108
    @115
    cvv
    wcel
    #
    @79
    @112
    cvv
    wcel
    @117
    @36
    cE
    fvex
    @112
    @114
    cvv
    difexg
    ax-mp
    a1i
    fvmptd
    adantl
    @79
    @110
    @116
    wceq
    wph
    @79
    @110
    @101
    @112
    cun
    #
    @101
    cdif
    #
    @116
    @79
    @39
    @118
    @31
    @101
    @79
    @39
    @102
    @118
    @109
    @79
    @61
    @112
    vi
    cM
    @28
    vi
    @112
    nfcv
    @87
    @60
    @36
    cE
    fveq2
    iunp1
    eqtrd
    @106
    difeq12d
    @119
    @116
    wceq
    @79
    @119
    @101
    @101
    cdif
    #
    @116
    cun
    c0
    @116
    cun
    @116
    @101
    @112
    @101
    difundir
    @120
    c0
    @116
    @101
    difid
    uneq1i
    @116
    0un
    3eqtri
    a1i
    eqtrd
    adantl
    3eqtr4d
    ineq2d
    @96
    @111
    wceq
    @85
    @111
    @96
    cA
    @39
    @31
    indif2
    eqcomi
    a1i
    eqtr4d
    fveq2d
    oveq12d
    @85
    @99
    @98
    @85
    @95
    cr
    wcel
    #
    @97
    cr
    wcel
    @99
    @98
    wceq
    wph
    @121
    @79
    wph
    cA
    @94
    cO
    cX
    carageniuncllem1.o
    carageniuncllem1.x
    carageniuncllem1.a
    carageniuncllem1.re
    @94
    cA
    wss
    wph
    @94
    @40
    cA
    @40
    @31
    inss1
    cA
    @39
    inss1
    #
    sstri
    a1i
    omessre
    adantr
    @85
    cA
    @96
    cO
    cX
    wph
    @90
    @79
    carageniuncllem1.o
    adantr
    #
    carageniuncllem1.x
    wph
    @91
    @79
    carageniuncllem1.a
    adantr
    wph
    @92
    @79
    carageniuncllem1.re
    adantr
    @96
    cA
    wss
    @85
    @96
    @40
    cA
    @40
    @31
    difss
    @122
    sstri
    a1i
    omessre
    @95
    @97
    rexadd
    syl2anc
    eqcomd
    @85
    @40
    cS
    @31
    cO
    cX
    @123
    carageniuncllem1.s
    carageniuncllem1.x
    @85
    @31
    @101
    cS
    @79
    @31
    @101
    wceq
    wph
    @106
    adantl
    wph
    @101
    cS
    wcel
    @79
    wph
    @29
    @61
    cS
    vi
    cO
    wph
    vi
    nfv
    carageniuncllem1.o
    carageniuncllem1.s
    wph
    cM
    @28
    fzfid
    wph
    @60
    @29
    wcel
    #
    wa
    cZ
    cS
    @60
    cE
    wph
    cZ
    cS
    cE
    wf
    @124
    carageniuncllem1.e
    adantr
    @124
    @60
    cZ
    wcel
    wph
    @124
    @60
    @11
    cZ
    @60
    cM
    @28
    elfzuz
    @11
    cZ
    wceq
    @124
    @107
    a1i
    eleqtrd
    adantl
    ffvelrnd
    caragenfiiuncl
    adantr
    eqeltrd
    wph
    @40
    cX
    wss
    @79
    wph
    cA
    @39
    cX
    carageniuncllem1.a
    ssinss1d
    adantr
    caragensplit
    3eqtrd
    3adant3
    3eqtrd
    syl3anc
    3exp
    fzind2
    sylc
end
