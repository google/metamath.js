include "cres.mm"
include "ctsu.mm"
include "co.mm"
include "cv.mm"
include "wcel.mm"
include "wss.mm"
include "cgsu.mm"
include "wi.mm"
include "cin.mm"
include "cpw.mm"
include "cfn.mm"
include "wral.mm"
include "wrex.mm"
include "ctopn.mm"
include "cfv.mm"
include "wa.mm"
include "inss1.mm"
include "sspwb.mm"
include "mpbi.mm"
include "ssrin.mm"
include "ax-mp.mm"
include "simpr.mm"
include "sseldi.mm"
include "elfpw.mm"
include "simplbi.mm"
include "adantl.mm"
include "syl.mm"
include "simprbi.mm"
include "ssfi.mm"
include "sylancl.mm"
include "sylanbrc.mm"
include "wceq.mm"
include "sseq2.mm"
include "ssin.mm"
include "syl6bbr.mm"
include "reseq2.mm"
include "inss2.mm"
include "resabs1.mm"
include "syl6eq.mm"
include "oveq2d.mm"
include "eleq1d.mm"
include "imbi12d.mm"
include "rspcv.mm"
include "ad2antlr.mm"
include "syl6ss.mm"
include "biantrud.mm"
include "resres.mm"
include "oveq2i.mm"
include "ccmn.mm"
include "ad2antrr.mm"
include "wf.mm"
include "fssresd.mm"
include "csupp.mm"
include "cvv.mm"
include "fex.mm"
include "syl2anc.mm"
include "c0g.mm"
include "fvex.mm"
include "eqeltri.mm"
include "ressuppss.mm"
include "sstrd.mm"
include "a1i.mm"
include "fdmfifsupp.mm"
include "gsumres.mm"
include "syl5reqr.mm"
include "sylibrd.mm"
include "ralrimdva.mm"
include "sseq1.mm"
include "imbi1d.mm"
include "ralbidv.mm"
include "rspcev.mm"
include "syl6an.mm"
include "rexlimdva.mm"
include "cun.mm"
include "unssd.mm"
include "unfi.mm"
include "syl2an.mm"
include "wb.mm"
include "ssun1.mm"
include "id.mm"
include "syl5sseqr.mm"
include "pm5.5.mm"
include "bitrd.mm"
include "adantrr.mm"
include "jctir.mm"
include "indir.mm"
include "df-ss.mm"
include "sylib.mm"
include "uneq2d.mm"
include "simprr.mm"
include "ssequn1.mm"
include "eqtrd.mm"
include "syl5eq.mm"
include "reseq2d.mm"
include "resabs1d.mm"
include "eqtr4d.mm"
include "eqtr3d.mm"
include "biimpd.mm"
include "expr.mm"
include "com23.mm"
include "syld.mm"
include "impbid.mm"
include "imbi2d.mm"
include "anbi2d.mm"
include "eqid.mm"
include "inex1g.mm"
include "fssres.mm"
include "wfn.mm"
include "ffn.mm"
include "fnresdm.mm"
include "3syl.mm"
include "reseq1d.mm"
include "syl5eqr.mm"
include "feq1d.mm"
include "mpbid.mm"
include "eltsms.mm"
include "3bitr4d.mm"
include "eqrdv.mm"

theorem tsmsres
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cF: class F
  let cG: class G
  let cV: class V
  let cW: class W
  let c.0: class .0.
  let va: setvar a
  let vb: setvar b
  let vu: setvar u
  let vy: setvar y
  let vz: setvar z
  let vx: setvar x
  assume tsmsres.b: |- B = ( Base ` G )
  assume tsmsres.z: |- .0. = ( 0g ` G )
  assume tsmsres.1: |- ( ph -> G e. CMnd )
  assume tsmsres.2: |- ( ph -> G e. TopSp )
  assume tsmsres.a: |- ( ph -> A e. V )
  assume tsmsres.f: |- ( ph -> F : A --> B )
  assume tsmsres.s: |- ( ph -> ( F supp .0. ) C_ W )


  assert |- ( ph -> ( G tsums ( F |` W ) ) = ( G tsums F ) )

  proof
    wph
    vx
    cG
    cF
    cW
    cres
    #
    ctsu
    co
    #
    cG
    cF
    ctsu
    co
    #
    wph
    vx
    cv
    #
    cB
    wcel
    #
    @3
    vu
    cv
    #
    wcel
    #
    va
    cv
    #
    vb
    cv
    #
    wss
    #
    cG
    @0
    @8
    cres
    #
    cgsu
    co
    #
    @5
    wcel
    #
    wi
    #
    vb
    cA
    cW
    cin
    #
    cpw
    #
    cfn
    cin
    #
    wral
    #
    va
    @16
    wrex
    #
    wi
    #
    vu
    cG
    ctopn
    cfv
    #
    wral
    #
    wa
    @4
    @6
    vy
    cv
    #
    vz
    cv
    #
    wss
    #
    cG
    cF
    @23
    cres
    #
    cgsu
    co
    #
    @5
    wcel
    #
    wi
    #
    vz
    cA
    cpw
    #
    cfn
    cin
    #
    wral
    #
    vy
    @30
    wrex
    #
    wi
    #
    vu
    @20
    wral
    #
    wa
    @3
    @1
    wcel
    @3
    @2
    wcel
    wph
    @21
    @34
    @4
    wph
    @19
    @33
    vu
    @20
    wph
    @18
    @32
    @6
    wph
    @18
    @32
    wph
    @17
    @32
    va
    @16
    wph
    @7
    @16
    wcel
    #
    wa
    #
    @7
    @30
    wcel
    @17
    @7
    @23
    wss
    #
    @27
    wi
    #
    vz
    @30
    wral
    #
    @32
    @36
    @16
    @30
    @7
    @15
    @29
    wss
    #
    @16
    @30
    wss
    @14
    cA
    wss
    #
    @40
    cA
    cW
    inss1
    #
    @14
    cA
    sspwb
    mpbi
    @15
    @29
    cfn
    ssrin
    ax-mp
    wph
    @35
    simpr
    sseldi
    @36
    @17
    @38
    vz
    @30
    @36
    @23
    @30
    wcel
    #
    wa
    #
    @17
    @37
    @7
    cW
    wss
    #
    wa
    #
    cG
    cF
    @23
    cW
    cin
    #
    cres
    #
    cgsu
    co
    #
    @5
    wcel
    #
    wi
    #
    @38
    @44
    @47
    @16
    wcel
    #
    @17
    @51
    wi
    @44
    @47
    @14
    wss
    #
    @47
    cfn
    wcel
    #
    @52
    @44
    @23
    cA
    wss
    #
    @53
    @43
    @55
    @36
    @43
    @55
    @23
    cfn
    wcel
    #
    @23
    cA
    elfpw
    #
    simplbi
    adantl
    #
    @23
    cA
    cW
    ssrin
    syl
    @44
    @56
    @47
    @23
    wss
    @54
    @43
    @56
    @36
    @43
    @55
    @56
    @57
    simprbi
    adantl
    #
    @23
    cW
    inss1
    @23
    @47
    ssfi
    sylancl
    @47
    @14
    elfpw
    sylanbrc
    @13
    @51
    vb
    @47
    @16
    @8
    @47
    wceq
    #
    @9
    @46
    @12
    @50
    @60
    @9
    @7
    @47
    wss
    @46
    @8
    @47
    @7
    sseq2
    @7
    @23
    cW
    ssin
    syl6bbr
    @60
    @11
    @49
    @5
    @60
    @10
    @48
    cG
    cgsu
    @60
    @10
    @0
    @47
    cres
    #
    @48
    @8
    @47
    @0
    reseq2
    @47
    cW
    wss
    @61
    @48
    wceq
    @23
    cW
    inss2
    cF
    @47
    cW
    resabs1
    ax-mp
    syl6eq
    oveq2d
    eleq1d
    imbi12d
    rspcv
    syl
    @44
    @37
    @46
    @27
    @50
    @44
    @45
    @37
    @44
    @7
    @14
    cW
    @35
    @7
    @14
    wss
    #
    wph
    @43
    @35
    @62
    @7
    cfn
    wcel
    @7
    @14
    elfpw
    simplbi
    ad2antlr
    cA
    cW
    inss2
    #
    syl6ss
    biantrud
    @44
    @26
    @49
    @5
    @44
    @49
    cG
    @25
    cW
    cres
    #
    cgsu
    co
    @26
    @64
    @48
    cG
    cgsu
    cF
    @23
    cW
    resres
    oveq2i
    @44
    @23
    cB
    @25
    cG
    cfn
    cW
    c.0
    tsmsres.b
    tsmsres.z
    wph
    cG
    ccmn
    wcel
    #
    @35
    @43
    tsmsres.1
    ad2antrr
    @59
    @44
    cA
    cB
    @23
    cF
    wph
    cA
    cB
    cF
    wf
    #
    @35
    @43
    tsmsres.f
    ad2antrr
    @58
    fssresd
    #
    @44
    @25
    c.0
    csupp
    co
    #
    cF
    c.0
    csupp
    co
    #
    cW
    @44
    cF
    cvv
    wcel
    #
    c.0
    cvv
    wcel
    #
    @68
    @69
    wss
    wph
    @70
    @35
    @43
    wph
    @66
    cA
    cV
    wcel
    #
    @70
    tsmsres.f
    tsmsres.a
    cA
    cB
    cV
    cF
    fex
    syl2anc
    #
    ad2antrr
    c.0
    cG
    c0g
    cfv
    cvv
    tsmsres.z
    cG
    c0g
    fvex
    eqeltri
    #
    @23
    cF
    cvv
    cvv
    c.0
    ressuppss
    sylancl
    wph
    @69
    cW
    wss
    #
    @35
    @43
    tsmsres.s
    ad2antrr
    sstrd
    @44
    @23
    cB
    @25
    cvv
    c.0
    @67
    @59
    @71
    @44
    @74
    a1i
    fdmfifsupp
    gsumres
    syl5reqr
    eleq1d
    imbi12d
    sylibrd
    ralrimdva
    @31
    @39
    vy
    @7
    @30
    @22
    @7
    wceq
    #
    @28
    @38
    vz
    @30
    @76
    @24
    @37
    @27
    @22
    @7
    @23
    sseq1
    imbi1d
    ralbidv
    rspcev
    syl6an
    rexlimdva
    wph
    @31
    @18
    vy
    @30
    wph
    @22
    @30
    wcel
    #
    wa
    #
    @22
    cW
    cin
    #
    @16
    wcel
    #
    @31
    @79
    @8
    wss
    #
    @12
    wi
    #
    vb
    @16
    wral
    #
    @18
    @78
    @79
    @14
    wss
    #
    @79
    cfn
    wcel
    #
    @80
    @78
    @22
    cA
    wss
    #
    @84
    @77
    @86
    wph
    @77
    @86
    @22
    cfn
    wcel
    #
    @22
    cA
    elfpw
    #
    simplbi
    #
    adantl
    @22
    cA
    cW
    ssrin
    syl
    @78
    @87
    @79
    @22
    wss
    @85
    @77
    @87
    wph
    @77
    @86
    @87
    @88
    simprbi
    adantl
    #
    @22
    cW
    inss1
    @22
    @79
    ssfi
    sylancl
    @79
    @14
    elfpw
    sylanbrc
    @78
    @31
    @82
    vb
    @16
    @78
    @8
    @16
    wcel
    #
    wa
    #
    @31
    cG
    cF
    @22
    @8
    cun
    #
    cres
    #
    cgsu
    co
    #
    @5
    wcel
    #
    @82
    @92
    @93
    @30
    wcel
    #
    @31
    @96
    wi
    @92
    @93
    cA
    wss
    #
    @93
    cfn
    wcel
    #
    @97
    @92
    @22
    @8
    cA
    @77
    @86
    wph
    @91
    @89
    ad2antlr
    @92
    @8
    @14
    cA
    @91
    @8
    @14
    wss
    #
    @78
    @91
    @100
    @8
    cfn
    wcel
    #
    @8
    @14
    elfpw
    #
    simplbi
    adantl
    #
    @42
    syl6ss
    unssd
    #
    @78
    @87
    @101
    @99
    @91
    @90
    @91
    @100
    @101
    @102
    simprbi
    @22
    @8
    unfi
    syl2an
    #
    @93
    cA
    elfpw
    sylanbrc
    @28
    @96
    vz
    @93
    @30
    @23
    @93
    wceq
    #
    @28
    @27
    @96
    @106
    @24
    @28
    @27
    wb
    @106
    @93
    @22
    @23
    @22
    @8
    ssun1
    @106
    id
    syl5sseqr
    @24
    @27
    pm5.5
    syl
    @106
    @26
    @95
    @5
    @106
    @25
    @94
    cG
    cgsu
    @23
    @93
    cF
    reseq2
    oveq2d
    eleq1d
    bitrd
    rspcv
    syl
    @92
    @81
    @96
    @12
    @78
    @91
    @81
    @96
    @12
    wi
    @78
    @91
    @81
    wa
    #
    wa
    #
    @96
    @12
    @108
    @95
    @11
    @5
    @108
    cG
    @94
    cW
    cres
    #
    cgsu
    co
    @95
    @11
    @108
    @93
    cB
    @94
    cG
    cfn
    cW
    c.0
    tsmsres.b
    tsmsres.z
    wph
    @65
    @77
    @107
    tsmsres.1
    ad2antrr
    @78
    @91
    @99
    @81
    @105
    adantrr
    #
    @108
    cA
    cB
    @93
    cF
    wph
    @66
    @77
    @107
    tsmsres.f
    ad2antrr
    @78
    @91
    @98
    @81
    @104
    adantrr
    fssresd
    #
    @108
    @94
    c.0
    csupp
    co
    #
    @69
    cW
    @108
    @70
    @71
    wa
    #
    @112
    @69
    wss
    wph
    @113
    @77
    @107
    wph
    @70
    @71
    @73
    @74
    jctir
    ad2antrr
    @93
    cF
    cvv
    cvv
    c.0
    ressuppss
    syl
    wph
    @75
    @77
    @107
    tsmsres.s
    ad2antrr
    sstrd
    @108
    @93
    cB
    @94
    cvv
    c.0
    @111
    @110
    @71
    @108
    @74
    a1i
    fdmfifsupp
    gsumres
    @108
    @109
    @10
    cG
    cgsu
    @108
    @109
    cF
    @8
    cres
    #
    @10
    @108
    @109
    cF
    @93
    cW
    cin
    #
    cres
    @114
    cF
    @93
    cW
    resres
    @108
    @115
    @8
    cF
    @108
    @115
    @79
    @8
    cW
    cin
    #
    cun
    #
    @8
    @22
    @8
    cW
    indir
    @108
    @117
    @79
    @8
    cun
    #
    @8
    @108
    @116
    @8
    @79
    @108
    @8
    cW
    wss
    #
    @116
    @8
    wceq
    @78
    @91
    @119
    @81
    @92
    @8
    @14
    cW
    @103
    @63
    syl6ss
    adantrr
    #
    @8
    cW
    df-ss
    sylib
    uneq2d
    @108
    @81
    @118
    @8
    wceq
    @78
    @91
    @81
    simprr
    @79
    @8
    ssequn1
    sylib
    eqtrd
    syl5eq
    reseq2d
    syl5eq
    @108
    cF
    @8
    cW
    @120
    resabs1d
    eqtr4d
    oveq2d
    eqtr3d
    eleq1d
    biimpd
    expr
    com23
    syld
    ralrimdva
    @17
    @83
    va
    @79
    @16
    @7
    @79
    wceq
    #
    @13
    @82
    vb
    @16
    @121
    @9
    @81
    @12
    @7
    @79
    @8
    sseq1
    imbi1d
    ralbidv
    rspcev
    syl6an
    rexlimdva
    impbid
    imbi2d
    ralbidv
    anbi2d
    wph
    vb
    va
    vu
    @14
    cB
    @3
    @16
    @0
    cG
    @20
    cvv
    tsmsres.b
    @20
    eqid
    #
    @16
    eqid
    tsmsres.1
    tsmsres.2
    wph
    @72
    @14
    cvv
    wcel
    tsmsres.a
    cA
    cW
    cV
    inex1g
    syl
    wph
    @14
    cB
    cF
    @14
    cres
    #
    wf
    #
    @14
    cB
    @0
    wf
    wph
    @66
    @41
    @124
    tsmsres.f
    @42
    cA
    cB
    @14
    cF
    fssres
    sylancl
    wph
    @14
    cB
    @123
    @0
    wph
    @123
    cF
    cA
    cres
    #
    cW
    cres
    @0
    cF
    cA
    cW
    resres
    wph
    @125
    cF
    cW
    wph
    @66
    cF
    cA
    wfn
    @125
    cF
    wceq
    tsmsres.f
    cA
    cB
    cF
    ffn
    cA
    cF
    fnresdm
    3syl
    reseq1d
    syl5eqr
    feq1d
    mpbid
    eltsms
    wph
    vz
    vy
    vu
    cA
    cB
    @3
    @30
    cF
    cG
    @20
    cV
    tsmsres.b
    @122
    @30
    eqid
    tsmsres.1
    tsmsres.2
    tsmsres.a
    tsmsres.f
    eltsms
    3bitr4d
    eqrdv
end
