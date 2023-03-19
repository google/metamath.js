include "cr.mm"
include "wcel.mm"
include "c1.mm"
include "cle.mm"
include "wbr.mm"
include "wa.mm"
include "cchp.mm"
include "cfv.mm"
include "ccht.mm"
include "cmin.mm"
include "co.mm"
include "csqrt.mm"
include "clog.mm"
include "cmul.mm"
include "caddc.mm"
include "cc0.mm"
include "cicc.mm"
include "cprime.mm"
include "cin.mm"
include "csu.mm"
include "chpcl.mm"
include "adantr.mm"
include "chtcl.mm"
include "resubcld.mm"
include "cfn.mm"
include "simpl.mm"
include "0red.mm"
include "1red.mm"
include "clt.mm"
include "0lt1.mm"
include "a1i.mm"
include "simpr.mm"
include "ltletrd.mm"
include "elrpd.mm"
include "rpge0d.mm"
include "resqrtcld.mm"
include "ppifi.mm"
include "syl.mm"
include "cv.mm"
include "crp.mm"
include "relogcld.mm"
include "fsumrecl.mm"
include "remulcld.mm"
include "cdiv.mm"
include "cfl.mm"
include "cn.mm"
include "inss2.mm"
include "sseldi.mm"
include "prmnn.mm"
include "nnrpd.mm"
include "nnred.mm"
include "c2.mm"
include "cuz.mm"
include "prmuz2.mm"
include "eluz2b2.mm"
include "simprbi.mm"
include "rplogcld.mm"
include "rerpdivcld.mm"
include "reflcl.mm"
include "recnd.mm"
include "fsumsub.mm"
include "wss.mm"
include "0le0.mm"
include "cexp.mm"
include "lemul2ad.mm"
include "sqsqrtd.mm"
include "mulid1d.mm"
include "eqtr4d.mm"
include "sqvald.mm"
include "3brtr4d.mm"
include "sqrtge0d.mm"
include "le2sqd.mm"
include "mpbird.mm"
include "iccss.mm"
include "syl22anc.mm"
include "ssrin.mm"
include "cc.mm"
include "sselda.mm"
include "syldan.mm"
include "cdif.mm"
include "wceq.mm"
include "eldifi.mm"
include "sylan2.mm"
include "mulid2d.mm"
include "w3a.mm"
include "inss1.mm"
include "wb.mm"
include "0re.mm"
include "elicc2.mm"
include "sylancr.mm"
include "mpbid.mm"
include "simp3d.mm"
include "logled.mm"
include "eqbrtrd.mm"
include "lemuldivd.mm"
include "wn.mm"
include "eldifn.mm"
include "adantl.mm"
include "elin.mm"
include "rbaib.mm"
include "df-3an.mm"
include "syl6bb.mm"
include "baibd.mm"
include "bitrd.mm"
include "mtbid.mm"
include "ltnled.mm"
include "lt2sqd.mm"
include "eqbrtrrd.mm"
include "nnsqcld.mm"
include "logltb.mm"
include "syl2anc.mm"
include "cz.mm"
include "2z.mm"
include "relogexp.mm"
include "sylancl.mm"
include "breqtrd.mm"
include "2re.mm"
include "ltdivmul2d.mm"
include "df-2.mm"
include "syl6breq.mm"
include "1z.mm"
include "flbi.mm"
include "mpbir2and.mm"
include "oveq2d.mm"
include "eqtrd.mm"
include "oveq1d.mm"
include "subidd.mm"
include "fsumss.mm"
include "chpval2.mm"
include "chtval.mm"
include "oveq12d.mm"
include "3eqtr4rd.mm"
include "subge02d.mm"
include "flle.mm"
include "lemuldiv2d.mm"
include "letrd.mm"
include "fsumle.mm"
include "chash.mm"
include "fsumconst.mm"
include "cn0.mm"
include "hashcl.mm"
include "nn0red.mm"
include "logge0.mm"
include "cfz.mm"
include "cdom.mm"
include "fzfid.mm"
include "ppisval.mm"
include "2eluzge1.mm"
include "fzss1.mm"
include "mp1i.mm"
include "syl5ss.mm"
include "eqsstrd.mm"
include "ssdomg.mm"
include "sylc.mm"
include "hashdom.mm"
include "flge0nn0.mm"
include "hashfz1.mm"
include "lemul1ad.mm"
include "lesubadd2d.mm"

theorem chpub
  let cA: class A
  let vd: setvar d
  let vk: setvar k
  let vm: setvar m
  let vn: setvar n
  let vp: setvar p
  let vx: setvar x


  assert |- ( ( A e. RR /\ 1 <_ A ) -> ( psi ` A ) <_ ( ( theta ` A ) + ( ( sqrt ` A ) x. ( log ` A ) ) ) )

  proof
    cA
    cr
    wcel
    #
    c1
    cA
    cle
    wbr
    #
    wa
    #
    cA
    cchp
    cfv
    #
    cA
    ccht
    cfv
    #
    cmin
    co
    #
    cA
    csqrt
    cfv
    #
    cA
    clog
    cfv
    #
    cmul
    co
    #
    cle
    wbr
    @3
    @4
    @8
    caddc
    co
    cle
    wbr
    @2
    @5
    cc0
    @6
    cicc
    co
    #
    cprime
    cin
    #
    @7
    vp
    csu
    #
    @8
    @2
    @3
    @4
    @0
    @3
    cr
    wcel
    @1
    cA
    chpcl
    adantr
    #
    @0
    @4
    cr
    wcel
    @1
    cA
    chtcl
    adantr
    #
    resubcld
    @2
    @10
    @7
    vp
    @2
    @6
    cr
    wcel
    #
    @10
    cfn
    wcel
    #
    @2
    cA
    @0
    @1
    simpl
    #
    @2
    cA
    @2
    cA
    @16
    @2
    cc0
    c1
    cA
    @2
    0red
    #
    @2
    1red
    #
    @16
    cc0
    c1
    clt
    wbr
    @2
    0lt1
    a1i
    @0
    @1
    simpr
    #
    ltletrd
    elrpd
    #
    rpge0d
    #
    resqrtcld
    #
    @6
    ppifi
    syl
    #
    @2
    vp
    cv
    #
    @10
    wcel
    #
    wa
    #
    cA
    @2
    cA
    crp
    wcel
    #
    @25
    @20
    adantr
    relogcld
    #
    fsumrecl
    @2
    @6
    @7
    @22
    @2
    cA
    @20
    relogcld
    #
    remulcld
    #
    @2
    @5
    @10
    @24
    clog
    cfv
    #
    @7
    @31
    cdiv
    co
    #
    cfl
    cfv
    #
    cmul
    co
    #
    @31
    cmin
    co
    #
    vp
    csu
    #
    @11
    cle
    @2
    cc0
    cA
    cicc
    co
    #
    cprime
    cin
    #
    @35
    vp
    csu
    @38
    @34
    vp
    csu
    #
    @38
    @31
    vp
    csu
    #
    cmin
    co
    @36
    @5
    @2
    @38
    @34
    @31
    vp
    @0
    @38
    cfn
    wcel
    @1
    cA
    ppifi
    adantr
    #
    @2
    @24
    @38
    wcel
    #
    wa
    #
    @34
    @43
    @31
    @33
    @43
    @24
    @43
    @24
    @43
    @24
    cprime
    wcel
    #
    @24
    cn
    wcel
    #
    @43
    @38
    cprime
    @24
    @37
    cprime
    inss2
    @2
    @42
    simpr
    #
    sseldi
    #
    @24
    prmnn
    #
    syl
    #
    nnrpd
    #
    relogcld
    #
    @43
    @32
    cr
    wcel
    #
    @33
    cr
    wcel
    #
    @43
    @7
    @31
    @2
    @7
    cr
    wcel
    #
    @42
    @29
    adantr
    @43
    @24
    @43
    @24
    @49
    nnred
    @43
    @24
    c2
    cuz
    cfv
    wcel
    #
    c1
    @24
    clt
    wbr
    #
    @43
    @44
    @55
    @47
    @24
    prmuz2
    syl
    @55
    @45
    @56
    @24
    eluz2b2
    simprbi
    syl
    rplogcld
    #
    rerpdivcld
    #
    @32
    reflcl
    syl
    #
    remulcld
    #
    recnd
    @43
    @31
    @51
    recnd
    #
    fsumsub
    @2
    @10
    @38
    @35
    vp
    @2
    @9
    @37
    wss
    #
    @10
    @38
    wss
    @2
    cc0
    cr
    wcel
    #
    @0
    cc0
    cc0
    cle
    wbr
    #
    @6
    cA
    cle
    wbr
    #
    @62
    @17
    @16
    @64
    @2
    0le0
    a1i
    @2
    @65
    @6
    c2
    cexp
    co
    #
    cA
    c2
    cexp
    co
    #
    cle
    wbr
    @2
    cA
    c1
    cmul
    co
    #
    cA
    cA
    cmul
    co
    @66
    @67
    cle
    @2
    c1
    cA
    cA
    @18
    @16
    @16
    @21
    @19
    lemul2ad
    @2
    @66
    cA
    @68
    @2
    cA
    @2
    cA
    @16
    recnd
    #
    sqsqrtd
    @2
    cA
    @69
    mulid1d
    eqtr4d
    @2
    cA
    @69
    sqvald
    3brtr4d
    @2
    @6
    cA
    @22
    @16
    @2
    cA
    @16
    @21
    sqrtge0d
    #
    @21
    le2sqd
    mpbird
    cc0
    cA
    cc0
    @6
    iccss
    syl22anc
    @9
    @37
    cprime
    ssrin
    syl
    #
    @2
    @25
    @42
    @35
    cc
    wcel
    @2
    @10
    @38
    @24
    @71
    sselda
    #
    @43
    @35
    @43
    @34
    @31
    @60
    @51
    resubcld
    #
    recnd
    syldan
    @2
    @24
    @38
    @10
    cdif
    wcel
    #
    wa
    #
    @35
    @31
    @31
    cmin
    co
    cc0
    @75
    @34
    @31
    @31
    cmin
    @75
    @34
    @31
    c1
    cmul
    co
    @31
    @75
    @33
    c1
    @31
    cmul
    @75
    @33
    c1
    wceq
    #
    c1
    @32
    cle
    wbr
    #
    @32
    c1
    c1
    caddc
    co
    #
    clt
    wbr
    #
    @75
    c1
    @31
    cmul
    co
    #
    @7
    cle
    wbr
    @77
    @75
    @80
    @31
    @7
    cle
    @75
    @31
    @74
    @2
    @42
    @31
    cc
    wcel
    @24
    @38
    @10
    eldifi
    #
    @61
    sylan2
    #
    mulid2d
    @75
    @24
    cA
    cle
    wbr
    #
    @31
    @7
    cle
    wbr
    @74
    @2
    @42
    @83
    @81
    @43
    @24
    cr
    wcel
    #
    cc0
    @24
    cle
    wbr
    #
    @83
    @43
    @24
    @37
    wcel
    #
    @84
    @85
    @83
    w3a
    #
    @43
    @38
    @37
    @24
    @37
    cprime
    inss1
    @46
    sseldi
    @43
    @63
    @0
    @86
    @87
    wb
    0re
    @2
    @0
    @42
    @16
    adantr
    cc0
    cA
    @24
    elicc2
    sylancr
    mpbid
    simp3d
    sylan2
    @75
    @24
    cA
    @74
    @2
    @42
    @24
    crp
    wcel
    #
    @81
    @50
    sylan2
    #
    @2
    @27
    @74
    @20
    adantr
    #
    logled
    mpbid
    eqbrtrd
    @75
    c1
    @7
    @31
    @75
    1red
    @2
    @54
    @74
    @29
    adantr
    #
    @74
    @2
    @42
    @31
    crp
    wcel
    #
    @81
    @57
    sylan2
    #
    lemuldivd
    mpbid
    @75
    @32
    c2
    @78
    clt
    @75
    @32
    c2
    clt
    wbr
    @7
    c2
    @31
    cmul
    co
    #
    clt
    wbr
    @75
    @7
    @24
    c2
    cexp
    co
    #
    clog
    cfv
    #
    @94
    clt
    @75
    cA
    @95
    clt
    wbr
    #
    @7
    @96
    clt
    wbr
    #
    @75
    @66
    cA
    @95
    clt
    @75
    cA
    @75
    cA
    @2
    @0
    @74
    @16
    adantr
    recnd
    sqsqrtd
    @75
    @6
    @24
    clt
    wbr
    #
    @66
    @95
    clt
    wbr
    @75
    @99
    @24
    @6
    cle
    wbr
    #
    wn
    @75
    @25
    @100
    @74
    @25
    wn
    @2
    @24
    @38
    @10
    eldifn
    adantl
    @75
    @25
    @24
    @9
    wcel
    #
    @100
    @75
    @44
    @25
    @101
    wb
    @74
    @2
    @42
    @44
    @81
    @47
    sylan2
    @25
    @101
    @44
    @24
    @9
    cprime
    elin
    rbaib
    syl
    @75
    @63
    @14
    @84
    @85
    @101
    @100
    wb
    @75
    0red
    @2
    @14
    @74
    @22
    adantr
    #
    @75
    @24
    @74
    @2
    @42
    @45
    @81
    @49
    sylan2
    #
    nnred
    #
    @75
    @24
    @89
    rpge0d
    #
    @63
    @14
    wa
    #
    @101
    @84
    @85
    wa
    #
    @100
    @106
    @101
    @84
    @85
    @100
    w3a
    @107
    @100
    wa
    cc0
    @6
    @24
    elicc2
    @84
    @85
    @100
    df-3an
    syl6bb
    baibd
    syl22anc
    bitrd
    mtbid
    @75
    @6
    @24
    @102
    @104
    ltnled
    mpbird
    @75
    @6
    @24
    @102
    @104
    @2
    cc0
    @6
    cle
    wbr
    #
    @74
    @70
    adantr
    @105
    lt2sqd
    mpbid
    eqbrtrrd
    @75
    @27
    @95
    crp
    wcel
    @97
    @98
    wb
    @90
    @75
    @95
    @75
    @24
    @103
    nnsqcld
    nnrpd
    cA
    @95
    logltb
    syl2anc
    mpbid
    @75
    @88
    c2
    cz
    wcel
    @96
    @94
    wceq
    @89
    2z
    @24
    c2
    relogexp
    sylancl
    breqtrd
    @75
    @7
    c2
    @31
    @91
    c2
    cr
    wcel
    @75
    2re
    a1i
    @93
    ltdivmul2d
    mpbird
    df-2
    syl6breq
    @75
    @52
    c1
    cz
    wcel
    @76
    @77
    @79
    wa
    wb
    @74
    @2
    @42
    @52
    @81
    @58
    sylan2
    1z
    @32
    c1
    flbi
    sylancl
    mpbir2and
    oveq2d
    @75
    @31
    @82
    mulid1d
    eqtrd
    oveq1d
    @75
    @31
    @82
    subidd
    eqtrd
    @41
    fsumss
    @2
    @3
    @39
    @4
    @40
    cmin
    @0
    @3
    @39
    wceq
    @1
    cA
    vp
    chpval2
    adantr
    @0
    @4
    @40
    wceq
    @1
    cA
    vp
    chtval
    adantr
    oveq12d
    3eqtr4rd
    @2
    @10
    @35
    @7
    vp
    @23
    @2
    @25
    @42
    @35
    cr
    wcel
    @72
    @73
    syldan
    #
    @28
    @26
    @35
    @34
    @7
    @109
    @2
    @25
    @42
    @34
    cr
    wcel
    @72
    @60
    syldan
    #
    @28
    @26
    cc0
    @31
    cle
    wbr
    @35
    @34
    cle
    wbr
    @26
    @31
    @2
    @25
    @42
    @92
    @72
    @57
    syldan
    #
    rpge0d
    @26
    @34
    @31
    @110
    @26
    @24
    @26
    @24
    @26
    @44
    @45
    @26
    @10
    cprime
    @24
    @9
    cprime
    inss2
    @2
    @25
    simpr
    sseldi
    @48
    syl
    nnrpd
    relogcld
    subge02d
    mpbid
    @26
    @34
    @7
    cle
    wbr
    @33
    @32
    cle
    wbr
    #
    @26
    @52
    @112
    @2
    @25
    @42
    @52
    @72
    @58
    syldan
    @32
    flle
    syl
    @26
    @33
    @7
    @31
    @2
    @25
    @42
    @53
    @72
    @59
    syldan
    @28
    @111
    lemuldiv2d
    mpbird
    letrd
    fsumle
    eqbrtrd
    @2
    @11
    @10
    chash
    cfv
    #
    @7
    cmul
    co
    #
    @8
    cle
    @2
    @15
    @7
    cc
    wcel
    @11
    @114
    wceq
    @23
    @2
    @7
    @29
    recnd
    @10
    @7
    vp
    fsumconst
    syl2anc
    @2
    @113
    @6
    @7
    @2
    @113
    @2
    @15
    @113
    cn0
    wcel
    @23
    @10
    hashcl
    syl
    nn0red
    #
    @22
    @29
    cA
    logge0
    @2
    @113
    @6
    cfl
    cfv
    #
    @6
    @115
    @2
    @14
    @116
    cr
    wcel
    @22
    @6
    reflcl
    syl
    @22
    @2
    @113
    c1
    @116
    cfz
    co
    #
    chash
    cfv
    #
    @116
    cle
    @2
    @113
    @118
    cle
    wbr
    #
    @10
    @117
    cdom
    wbr
    #
    @2
    @117
    cfn
    wcel
    #
    @10
    @117
    wss
    @120
    @2
    c1
    @116
    fzfid
    #
    @2
    @10
    c2
    @116
    cfz
    co
    #
    cprime
    cin
    #
    @117
    @2
    @14
    @10
    @124
    wceq
    @22
    @6
    ppisval
    syl
    @2
    @124
    @123
    @117
    @123
    cprime
    inss1
    c2
    c1
    cuz
    cfv
    wcel
    @123
    @117
    wss
    @2
    2eluzge1
    c2
    c1
    @116
    fzss1
    mp1i
    syl5ss
    eqsstrd
    @10
    @117
    cfn
    ssdomg
    sylc
    @2
    @15
    @121
    @119
    @120
    wb
    @23
    @122
    @10
    @117
    cfn
    hashdom
    syl2anc
    mpbird
    @2
    @116
    cn0
    wcel
    #
    @118
    @116
    wceq
    @2
    @14
    @108
    @125
    @22
    @70
    @6
    flge0nn0
    syl2anc
    @116
    hashfz1
    syl
    breqtrd
    @2
    @14
    @116
    @6
    cle
    wbr
    @22
    @6
    flle
    syl
    letrd
    lemul1ad
    eqbrtrd
    letrd
    @2
    @3
    @4
    @8
    @12
    @13
    @30
    lesubadd2d
    mpbid
end
