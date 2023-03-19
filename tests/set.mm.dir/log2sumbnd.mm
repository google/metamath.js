include "crp.mm"
include "wcel.mm"
include "c1.mm"
include "cle.mm"
include "wbr.mm"
include "wa.mm"
include "cfl.mm"
include "cfv.mm"
include "cfz.mm"
include "co.mm"
include "cv.mm"
include "clog.mm"
include "c2.mm"
include "cexp.mm"
include "csu.mm"
include "cmul.mm"
include "cmin.mm"
include "caddc.mm"
include "cabs.mm"
include "cneg.mm"
include "cr.mm"
include "fzfid.mm"
include "cn.mm"
include "elfznn.mm"
include "adantl.mm"
include "nnrpd.mm"
include "relogcld.mm"
include "resqcld.mm"
include "fsumrecl.mm"
include "rpre.mm"
include "adantr.mm"
include "relogcl.mm"
include "2re.mm"
include "remulcl.mm"
include "sylancr.mm"
include "resubcl.mm"
include "readdcld.mm"
include "remulcld.mm"
include "resubcld.mm"
include "recnd.mm"
include "abscld.mm"
include "sylancl.mm"
include "cc.mm"
include "2cn.mm"
include "negcli.mm"
include "subcl.mm"
include "absnegi.mm"
include "cc0.mm"
include "wceq.mm"
include "0le2.mm"
include "absid.mm"
include "mp2an.mm"
include "eqtri.mm"
include "oveq2i.mm"
include "abs2dif.mm"
include "syl5eqbrr.mm"
include "cmpt.mm"
include "fveq2.mm"
include "oveq2d.mm"
include "sumeq1d.mm"
include "id.mm"
include "oveq1d.mm"
include "oveq12d.mm"
include "eqid.mm"
include "ovex.mm"
include "fvmpt3i.mm"
include "1rp.mm"
include "cz.mm"
include "1z.mm"
include "flid.mm"
include "ax-mp.mm"
include "syl6eq.mm"
include "0cn.mm"
include "log1.mm"
include "sq0id.mm"
include "fsum1.mm"
include "2t0e0.mm"
include "subid1i.mm"
include "addid2i.mm"
include "mulid2i.mm"
include "df-neg.mm"
include "syl6eqr.mm"
include "mp1i.mm"
include "fveq2d.mm"
include "cpnf.mm"
include "cioo.mm"
include "ioorp.mm"
include "eqcomi.mm"
include "nnuz.mm"
include "a1i.mm"
include "1red.mm"
include "cxr.mm"
include "pnfxr.mm"
include "1re.mm"
include "1nn0.mm"
include "nn0addge1i.mm"
include "0red.mm"
include "simpr.mm"
include "nnrp.mm"
include "sylan2.mm"
include "cdv.mm"
include "cdiv.mm"
include "cpr.mm"
include "reelprrecn.mm"
include "crn.mm"
include "ctg.mm"
include "ccnfld.mm"
include "ctopn.mm"
include "recn.mm"
include "dvmptid.mm"
include "wss.mm"
include "rpssre.mm"
include "tgioo2.mm"
include "iooretop.mm"
include "eqeltrri.mm"
include "dvmptres.mm"
include "rerpdivcld.mm"
include "cvv.mm"
include "rpreccld.mm"
include "rpcnd.mm"
include "mulcld.mm"
include "cnelprrecn.mm"
include "sqcl.mm"
include "mulcl.mm"
include "cres.mm"
include "dvrelog.mm"
include "wf1o.mm"
include "wf.mm"
include "relogf1o.mm"
include "f1of.mm"
include "feqmptd.mm"
include "fvres.mm"
include "mpteq2ia.mm"
include "syl5reqr.mm"
include "2nn.mm"
include "dvexp.mm"
include "2m1e1.mm"
include "exp1.mm"
include "syl5eq.mm"
include "oveq1.mm"
include "oveq2.mm"
include "dvmptco.mm"
include "ovexd.mm"
include "2cnd.mm"
include "dvmptc.mm"
include "dvmptcmul.mm"
include "dvmptsub.mm"
include "dvmptadd.mm"
include "subdird.mm"
include "wne.mm"
include "rpne0.mm"
include "divrecd.mm"
include "negsubd.mm"
include "syl5eqr.mm"
include "3eqtr4rd.mm"
include "mpteq2dva.mm"
include "eqtrd.mm"
include "dvmptmul.mm"
include "mulid2d.mm"
include "subsub2d.mm"
include "eqtr4d.mm"
include "divcan1d.mm"
include "npcand.mm"
include "w3a.mm"
include "simp32.mm"
include "simp2l.mm"
include "simp2r.mm"
include "logled.mm"
include "mpbid.mm"
include "simp31.mm"
include "wb.mm"
include "logleb.mm"
include "rpred.mm"
include "letrd.mm"
include "logge0d.mm"
include "le2sqd.mm"
include "ad2antrl.mm"
include "sqge0d.mm"
include "simpl.mm"
include "1le1.mm"
include "rexrd.mm"
include "pnfge.mm"
include "syl.mm"
include "dvfsum2.mm"
include "eqbrtrrd.mm"
include "lesubaddd.mm"

theorem log2sumbnd
  let cA: class A
  let vn: setvar n
  let vx: setvar x
  let vy: setvar y

  disjoint A n
  disjoint n x
  disjoint n y
  disjoint x y
  disjoint A x
  disjoint A y
  assert |- ( ( A e. RR+ /\ 1 <_ A ) -> ( abs ` ( sum_ n e. ( 1 ... ( |_ ` A ) ) ( ( log ` n ) ^ 2 ) - ( A x. ( ( ( log ` A ) ^ 2 ) + ( 2 - ( 2 x. ( log ` A ) ) ) ) ) ) ) <_ ( ( ( log ` A ) ^ 2 ) + 2 ) )

  proof
    cA
    crp
    wcel
    #
    c1
    cA
    cle
    wbr
    #
    wa
    #
    c1
    cA
    cfl
    cfv
    #
    cfz
    co
    #
    vn
    cv
    #
    clog
    cfv
    #
    c2
    cexp
    co
    #
    vn
    csu
    #
    cA
    cA
    clog
    cfv
    #
    c2
    cexp
    co
    #
    c2
    c2
    @9
    cmul
    co
    #
    cmin
    co
    #
    caddc
    co
    #
    cmul
    co
    #
    cmin
    co
    #
    cabs
    cfv
    #
    c2
    cmin
    co
    #
    @10
    cle
    wbr
    @16
    @10
    c2
    caddc
    co
    cle
    wbr
    @2
    @17
    @15
    c2
    cneg
    #
    cmin
    co
    #
    cabs
    cfv
    #
    @10
    @2
    @16
    cr
    wcel
    c2
    cr
    wcel
    #
    @17
    cr
    wcel
    @2
    @15
    @2
    @15
    @2
    @8
    @14
    @2
    @4
    @7
    vn
    @2
    c1
    @3
    fzfid
    @2
    @5
    @4
    wcel
    #
    wa
    #
    @6
    @23
    @5
    @23
    @5
    @22
    @5
    cn
    wcel
    @2
    @5
    @3
    elfznn
    adantl
    nnrpd
    relogcld
    resqcld
    fsumrecl
    @2
    cA
    @13
    @0
    cA
    cr
    wcel
    @1
    cA
    rpre
    adantr
    #
    @2
    @10
    @12
    @2
    @9
    @0
    @9
    cr
    wcel
    #
    @1
    cA
    relogcl
    adantr
    #
    resqcld
    #
    @2
    @21
    @11
    cr
    wcel
    #
    @12
    cr
    wcel
    2re
    @2
    @21
    @25
    @28
    2re
    @26
    c2
    @9
    remulcl
    sylancr
    c2
    @11
    resubcl
    sylancr
    readdcld
    remulcld
    resubcld
    recnd
    #
    abscld
    #
    2re
    @16
    c2
    resubcl
    sylancl
    @2
    @19
    @2
    @15
    cc
    wcel
    #
    @18
    cc
    wcel
    #
    @19
    cc
    wcel
    @29
    c2
    2cn
    negcli
    #
    @15
    @18
    subcl
    sylancl
    abscld
    @27
    @2
    @17
    @16
    @18
    cabs
    cfv
    #
    cmin
    co
    #
    @20
    cle
    @34
    c2
    @16
    cmin
    @34
    c2
    cabs
    cfv
    #
    c2
    c2
    2cn
    absnegi
    @21
    cc0
    c2
    cle
    wbr
    @36
    c2
    wceq
    2re
    0le2
    c2
    absid
    mp2an
    eqtri
    oveq2i
    @2
    @31
    @32
    @35
    @20
    cle
    wbr
    @29
    @33
    @15
    @18
    abs2dif
    sylancl
    syl5eqbrr
    @2
    cA
    vx
    crp
    c1
    vx
    cv
    #
    cfl
    cfv
    #
    cfz
    co
    #
    @7
    vn
    csu
    #
    @37
    @37
    clog
    cfv
    #
    c2
    cexp
    co
    #
    c2
    c2
    @41
    cmul
    co
    #
    cmin
    co
    #
    caddc
    co
    #
    cmul
    co
    #
    cmin
    co
    #
    cmpt
    #
    cfv
    #
    c1
    @48
    cfv
    #
    cmin
    co
    #
    cabs
    cfv
    @20
    @10
    cle
    @2
    @51
    @19
    cabs
    @2
    @49
    @15
    @50
    @18
    cmin
    @0
    @49
    @15
    wceq
    @1
    vx
    cA
    @47
    @15
    crp
    @48
    @37
    cA
    wceq
    #
    @40
    @8
    @46
    @14
    cmin
    @52
    @39
    @4
    @7
    vn
    @52
    @38
    @3
    c1
    cfz
    @37
    cA
    cfl
    fveq2
    oveq2d
    sumeq1d
    @52
    @37
    cA
    @45
    @13
    cmul
    @52
    id
    @52
    @42
    @10
    @44
    @12
    caddc
    @52
    @41
    @9
    c2
    cexp
    @37
    cA
    clog
    fveq2
    #
    oveq1d
    #
    @52
    @43
    @11
    c2
    cmin
    @52
    @41
    @9
    c2
    cmul
    @53
    oveq2d
    oveq2d
    oveq12d
    oveq12d
    oveq12d
    @48
    eqid
    #
    @40
    @46
    cmin
    ovex
    #
    fvmpt3i
    adantr
    c1
    crp
    wcel
    #
    @50
    @18
    wceq
    @2
    1rp
    vx
    c1
    @47
    @18
    crp
    @48
    @37
    c1
    wceq
    #
    @47
    cc0
    c2
    cmin
    co
    @18
    @58
    @40
    cc0
    @46
    c2
    cmin
    @58
    @40
    c1
    c1
    cfz
    co
    #
    @7
    vn
    csu
    #
    cc0
    @58
    @39
    @59
    @7
    vn
    @58
    @38
    c1
    c1
    cfz
    @58
    @38
    c1
    cfl
    cfv
    #
    c1
    @37
    c1
    cfl
    fveq2
    c1
    cz
    wcel
    #
    @61
    c1
    wceq
    1z
    c1
    flid
    ax-mp
    syl6eq
    oveq2d
    sumeq1d
    @62
    cc0
    cc
    wcel
    @60
    cc0
    wceq
    1z
    0cn
    @7
    cc0
    vn
    c1
    @5
    c1
    wceq
    #
    @6
    @63
    @6
    c1
    clog
    cfv
    #
    cc0
    @5
    c1
    clog
    fveq2
    log1
    syl6eq
    sq0id
    fsum1
    mp2an
    syl6eq
    @58
    @46
    c1
    c2
    cmul
    co
    c2
    @58
    @37
    c1
    @45
    c2
    cmul
    @58
    id
    @58
    @45
    cc0
    c2
    caddc
    co
    c2
    @58
    @42
    cc0
    @44
    c2
    caddc
    @58
    @41
    @58
    @41
    @64
    cc0
    @37
    c1
    clog
    fveq2
    log1
    syl6eq
    #
    sq0id
    @58
    @44
    c2
    cc0
    cmin
    co
    c2
    @58
    @43
    cc0
    c2
    cmin
    @58
    @43
    c2
    cc0
    cmul
    co
    cc0
    @58
    @41
    cc0
    c2
    cmul
    @65
    oveq2d
    2t0e0
    syl6eq
    oveq2d
    c2
    2cn
    subid1i
    syl6eq
    oveq12d
    c2
    2cn
    addid2i
    syl6eq
    oveq12d
    c2
    2cn
    mulid2i
    syl6eq
    oveq12d
    c2
    df-neg
    syl6eqr
    @55
    @56
    fvmpt3i
    mp1i
    oveq12d
    fveq2d
    @2
    vx
    @46
    @42
    @7
    c1
    crp
    cc0
    cpnf
    vn
    @10
    @48
    c1
    cr
    c1
    cA
    cn
    cc0
    cpnf
    cioo
    co
    #
    crp
    ioorp
    eqcomi
    nnuz
    @62
    @2
    1z
    a1i
    @2
    1red
    cpnf
    cxr
    wcel
    @2
    pnfxr
    a1i
    c1
    c1
    c1
    caddc
    co
    cle
    wbr
    @2
    c1
    c1
    1re
    1nn0
    nn0addge1i
    a1i
    @2
    0red
    @2
    @37
    crp
    wcel
    #
    wa
    #
    @37
    @45
    @67
    @37
    cr
    wcel
    #
    @2
    @37
    rpre
    adantl
    #
    @68
    @42
    @44
    @68
    @41
    @68
    @37
    @2
    @67
    simpr
    #
    relogcld
    #
    resqcld
    #
    @68
    @21
    @43
    cr
    wcel
    #
    @44
    cr
    wcel
    2re
    @68
    @21
    @41
    cr
    wcel
    #
    @74
    2re
    @72
    c2
    @41
    remulcl
    sylancr
    #
    c2
    @43
    resubcl
    sylancr
    #
    readdcld
    #
    remulcld
    @73
    @37
    cn
    wcel
    @2
    @67
    @42
    cr
    wcel
    @37
    nnrp
    @73
    sylan2
    @2
    cr
    vx
    crp
    @46
    cmpt
    cdv
    co
    vx
    crp
    c1
    @45
    cmul
    co
    #
    @43
    c2
    cmin
    co
    #
    @37
    cdiv
    co
    #
    @37
    cmul
    co
    #
    caddc
    co
    #
    cmpt
    vx
    crp
    @42
    cmpt
    @2
    vx
    @37
    c1
    @45
    @81
    cr
    cr
    cr
    crp
    cr
    cr
    cc
    cpr
    #
    wcel
    @2
    reelprrecn
    a1i
    #
    @68
    @37
    @70
    recnd
    #
    @68
    1red
    @2
    vx
    @37
    c1
    cr
    cioo
    crn
    ctg
    cfv
    #
    ccnfld
    ctopn
    cfv
    #
    cr
    cr
    crp
    @85
    @69
    @37
    cc
    wcel
    @2
    @37
    recn
    adantl
    @2
    @69
    wa
    #
    1red
    @2
    vx
    cr
    @85
    dvmptid
    crp
    cr
    wss
    @2
    rpssre
    a1i
    #
    @88
    @88
    eqid
    #
    tgioo2
    #
    @91
    crp
    @87
    wcel
    @2
    @66
    crp
    @87
    ioorp
    cc0
    cpnf
    iooretop
    eqeltrri
    a1i
    #
    dvmptres
    @68
    @45
    @78
    recnd
    #
    @68
    @80
    @37
    @68
    @74
    @21
    @80
    cr
    wcel
    @76
    2re
    @43
    c2
    resubcl
    sylancl
    #
    @71
    rerpdivcld
    @2
    cr
    vx
    crp
    @45
    cmpt
    cdv
    co
    vx
    crp
    @43
    c1
    @37
    cdiv
    co
    #
    cmul
    co
    #
    cc0
    c2
    @96
    cmul
    co
    #
    cmin
    co
    #
    caddc
    co
    #
    cmpt
    vx
    crp
    @81
    cmpt
    @2
    vx
    @42
    @97
    @44
    @99
    cr
    cc
    cvv
    crp
    @85
    @68
    @42
    @73
    recnd
    #
    @68
    @43
    @96
    @68
    @43
    @76
    recnd
    #
    @68
    @96
    @68
    @37
    @71
    rpreccld
    #
    rpcnd
    #
    mulcld
    #
    @2
    vx
    vy
    @41
    @96
    vy
    cv
    #
    c2
    cexp
    co
    #
    c2
    @106
    cmul
    co
    #
    cr
    cc
    @42
    @43
    crp
    cc
    crp
    cc
    @85
    cc
    @84
    wcel
    @2
    cnelprrecn
    a1i
    @68
    @41
    @72
    recnd
    #
    @103
    @106
    cc
    wcel
    #
    @107
    cc
    wcel
    @2
    @106
    sqcl
    adantl
    @2
    @110
    wa
    c2
    cc
    wcel
    #
    @110
    @108
    cc
    wcel
    2cn
    @2
    @110
    simpr
    c2
    @106
    mulcl
    sylancr
    @2
    vx
    crp
    @96
    cmpt
    cr
    clog
    crp
    cres
    #
    cdv
    co
    cr
    vx
    crp
    @41
    cmpt
    #
    cdv
    co
    vx
    dvrelog
    @2
    @112
    @113
    cr
    cdv
    @2
    @112
    vx
    crp
    @37
    @112
    cfv
    #
    cmpt
    @113
    @2
    vx
    crp
    cr
    @112
    crp
    cr
    @112
    wf1o
    crp
    cr
    @112
    wf
    @2
    relogf1o
    crp
    cr
    @112
    f1of
    mp1i
    feqmptd
    vx
    crp
    @114
    @41
    @37
    crp
    clog
    fvres
    mpteq2ia
    syl6eq
    oveq2d
    syl5reqr
    #
    @2
    cc
    vy
    cc
    @107
    cmpt
    cdv
    co
    #
    vy
    cc
    c2
    @106
    c2
    c1
    cmin
    co
    #
    cexp
    co
    #
    cmul
    co
    #
    cmpt
    #
    vy
    cc
    @108
    cmpt
    c2
    cn
    wcel
    @116
    @120
    wceq
    @2
    2nn
    vy
    c2
    dvexp
    mp1i
    vy
    cc
    @119
    @108
    @110
    @118
    @106
    c2
    cmul
    @110
    @118
    @106
    c1
    cexp
    co
    @106
    @117
    c1
    @106
    cexp
    2m1e1
    oveq2i
    @106
    exp1
    syl5eq
    oveq2d
    mpteq2ia
    syl6eq
    @106
    @41
    c2
    cexp
    oveq1
    @106
    @41
    c2
    cmul
    oveq2
    dvmptco
    @68
    @44
    @77
    recnd
    @68
    cc0
    @98
    cmin
    ovexd
    @2
    vx
    c2
    cc0
    @43
    @98
    cr
    cr
    cc
    crp
    @85
    @68
    2cnd
    #
    @68
    0red
    @2
    vx
    c2
    cc0
    cr
    @87
    @88
    cr
    cr
    crp
    @85
    @89
    2cnd
    @89
    0red
    @2
    vx
    c2
    cr
    @85
    @2
    2cnd
    #
    dvmptc
    @90
    @92
    @91
    @93
    dvmptres
    @102
    @68
    @111
    @96
    cc
    wcel
    @98
    cc
    wcel
    2cn
    @104
    c2
    @96
    mulcl
    sylancr
    #
    @2
    vx
    @41
    @96
    c2
    cr
    crp
    crp
    @85
    @109
    @103
    @115
    @122
    dvmptcmul
    dvmptsub
    dvmptadd
    @2
    vx
    crp
    @100
    @81
    @68
    @80
    @96
    cmul
    co
    @97
    @98
    cmin
    co
    #
    @81
    @100
    @68
    @43
    c2
    @96
    @102
    @121
    @104
    subdird
    @68
    @80
    @37
    @68
    @80
    @95
    recnd
    #
    @86
    @67
    @37
    cc0
    wne
    @2
    @37
    rpne0
    adantl
    #
    divrecd
    @68
    @100
    @97
    @98
    cneg
    #
    caddc
    co
    @124
    @127
    @99
    @97
    caddc
    @98
    df-neg
    oveq2i
    @68
    @97
    @98
    @105
    @123
    negsubd
    syl5eqr
    3eqtr4rd
    mpteq2dva
    eqtrd
    dvmptmul
    @2
    vx
    crp
    @83
    @42
    @68
    @83
    @42
    @80
    cmin
    co
    #
    @80
    caddc
    co
    @42
    @68
    @79
    @128
    @82
    @80
    caddc
    @68
    @79
    @45
    @128
    @68
    @45
    @94
    mulid2d
    @68
    @42
    @43
    c2
    @101
    @102
    @121
    subsub2d
    eqtr4d
    @68
    @80
    @37
    @125
    @86
    @126
    divcan1d
    oveq12d
    @68
    @42
    @80
    @101
    @125
    npcand
    eqtrd
    mpteq2dva
    eqtrd
    @37
    @5
    wceq
    @41
    @6
    c2
    cexp
    @37
    @5
    clog
    fveq2
    oveq1d
    @2
    @67
    @5
    crp
    wcel
    #
    wa
    #
    c1
    @37
    cle
    wbr
    #
    @37
    @5
    cle
    wbr
    #
    @5
    cpnf
    cle
    wbr
    #
    w3a
    #
    w3a
    #
    @41
    @6
    cle
    wbr
    #
    @42
    @7
    cle
    wbr
    @135
    @132
    @136
    @2
    @130
    @131
    @132
    @133
    simp32
    #
    @135
    @37
    @5
    @2
    @67
    @129
    @134
    simp2l
    #
    @2
    @67
    @129
    @134
    simp2r
    #
    logled
    mpbid
    @135
    @41
    @6
    @135
    @37
    @138
    relogcld
    @135
    @5
    @139
    relogcld
    @135
    cc0
    @64
    @41
    cle
    log1
    @135
    @131
    @64
    @41
    cle
    wbr
    #
    @2
    @130
    @131
    @132
    @133
    simp31
    #
    @135
    @57
    @67
    @131
    @140
    wb
    1rp
    @138
    c1
    @37
    logleb
    sylancr
    mpbid
    syl5eqbrr
    @135
    @5
    @135
    @5
    @139
    rpred
    #
    @135
    c1
    @37
    @5
    @135
    1red
    @135
    @37
    @138
    rpred
    @142
    @141
    @137
    letrd
    logge0d
    le2sqd
    mpbid
    @55
    @2
    @67
    @131
    wa
    wa
    @41
    @67
    @75
    @2
    @131
    @37
    relogcl
    ad2antrl
    sqge0d
    @57
    @2
    1rp
    a1i
    @0
    @1
    simpl
    c1
    c1
    cle
    wbr
    @2
    1le1
    a1i
    @0
    @1
    simpr
    @2
    cA
    cxr
    wcel
    cA
    cpnf
    cle
    wbr
    @2
    cA
    @24
    rexrd
    cA
    pnfge
    syl
    @54
    dvfsum2
    eqbrtrrd
    letrd
    @2
    @16
    c2
    @10
    @30
    @21
    @2
    2re
    a1i
    @27
    lesubaddd
    mpbid
end
