include "cfv.mm"
include "cr.mm"
include "cv.mm"
include "c2.mm"
include "cpi.mm"
include "cmul.mm"
include "co.mm"
include "cmo.mm"
include "cc0.mm"
include "wceq.mm"
include "c1.mm"
include "caddc.mm"
include "cdiv.mm"
include "csin.mm"
include "cif.mm"
include "cmpt.mm"
include "a1i.mm"
include "cn.mm"
include "wcel.mm"
include "dirkerval.mm"
include "syl.mm"
include "cfz.mm"
include "ccos.mm"
include "csu.mm"
include "wa.mm"
include "cc.mm"
include "2cnd.mm"
include "nncnd.mm"
include "mulcld.mm"
include "peano2cn.mm"
include "picn.mm"
include "wne.mm"
include "2ne0.mm"
include "pire.mm"
include "pipos.mm"
include "gt0ne0ii.mm"
include "divdiv1d.mm"
include "eqcomd.mm"
include "ad2antrr.mm"
include "iftrue.mm"
include "adantl.mm"
include "chash.mm"
include "wral.mm"
include "cz.mm"
include "elfzelz.mm"
include "zcnd.mm"
include "recn.mm"
include "2cn.mm"
include "mulcli.mm"
include "mulne0i.mm"
include "divassd.mm"
include "simpr.mm"
include "crp.mm"
include "wb.mm"
include "simpl.mm"
include "2rp.mm"
include "pirp.mm"
include "rpmulcl.mm"
include "mp2an.mm"
include "mod0.mm"
include "sylancl.mm"
include "mpbid.mm"
include "adantr.mm"
include "zmulcld.mm"
include "eqeltrd.mm"
include "coseq1.mm"
include "adantlr.mm"
include "mpbird.mm"
include "ralrimiva.mm"
include "adantll.mm"
include "sumeq2d.mm"
include "cfn.mm"
include "fzfid.mm"
include "1cnd.mm"
include "fsumconst.mm"
include "syl2anc.mm"
include "cn0.mm"
include "nnnn0d.mm"
include "hashfz1.mm"
include "oveq1d.mm"
include "mulid1d.mm"
include "eqtrd.mm"
include "3eqtrd.mm"
include "oveq2d.mm"
include "div1d.mm"
include "ax-1ne0.mm"
include "divadddivd.mm"
include "addcomd.mm"
include "mulcomd.mm"
include "oveq12d.mm"
include "3eqtr4rd.mm"
include "wn.mm"
include "iffalse.mm"
include "cfl.mm"
include "divcan1d.mm"
include "rpreccl.mm"
include "ax-mp.mm"
include "moddi.mm"
include "mp3an13.mm"
include "divrec2d.mm"
include "reccld.mm"
include "mulassd.mm"
include "recidi.mm"
include "oveq2i.mm"
include "syl5eq.mm"
include "eqtr2d.mm"
include "id.mm"
include "modcld.mm"
include "recnd.mm"
include "ax-1cn.mm"
include "divne0i.mm"
include "neqne.mm"
include "mulne0d.mm"
include "eqnetrd.mm"
include "oddfl.mm"
include "fveq2d.mm"
include "sumeq2sdv.mm"
include "adantlll.mm"
include "redivcld.mm"
include "rehalfcld.mm"
include "flcld.mm"
include "ad2antlr.mm"
include "eqid.mm"
include "dirkertrigeqlem3.mm"
include "3eqtrrd.mm"
include "simplr.mm"
include "mtbid.mm"
include "sineq0.mm"
include "mtbird.mm"
include "neqned.mm"
include "dirkertrigeqlem2.mm"
include "pm2.61dan.mm"
include "mpteq2dva.mm"
include "syl5req.mm"

theorem dirkertrigeq
  let wph: wff ph
  let cD: class D
  let vk: setvar k
  let vn: setvar n
  let cF: class F
  let cH: class H
  let cN: class N
  let vs: setvar s
  let vx: setvar x
  assume dirkertrigeq.d: |- D = ( n e. NN |-> ( s e. RR |-> if ( ( s mod ( 2 x. _pi ) ) = 0 , ( ( ( 2 x. n ) + 1 ) / ( 2 x. _pi ) ) , ( ( sin ` ( ( n + ( 1 / 2 ) ) x. s ) ) / ( ( 2 x. _pi ) x. ( sin ` ( s / 2 ) ) ) ) ) ) )
  assume dirkertrigeq.n: |- ( ph -> N e. NN )
  assume dirkertrigeq.f: |- F = ( D ` N )
  assume dirkertrigeq.h: |- H = ( s e. RR |-> ( ( ( 1 / 2 ) + sum_ k e. ( 1 ... N ) ( cos ` ( k x. s ) ) ) / _pi ) )

  disjoint N k
  disjoint N s
  disjoint k s
  disjoint k ph
  disjoint ph s
  disjoint n s
  disjoint k x
  assert |- ( ph -> F = H )

  proof
    wph
    cF
    cN
    cD
    cfv
    #
    vs
    cr
    vs
    cv
    #
    c2
    cpi
    cmul
    co
    #
    cmo
    co
    #
    cc0
    wceq
    #
    c2
    cN
    cmul
    co
    #
    c1
    caddc
    co
    #
    @2
    cdiv
    co
    #
    cN
    c1
    c2
    cdiv
    co
    #
    caddc
    co
    #
    @1
    cmul
    co
    #
    csin
    cfv
    #
    @2
    @1
    c2
    cdiv
    co
    #
    csin
    cfv
    #
    cmul
    co
    #
    cdiv
    co
    #
    cif
    #
    cmpt
    #
    cH
    cF
    @0
    wceq
    wph
    dirkertrigeq.f
    a1i
    wph
    cN
    cn
    wcel
    #
    @0
    @17
    wceq
    dirkertrigeq.n
    cD
    vn
    cN
    vs
    dirkertrigeq.d
    dirkerval
    syl
    wph
    cH
    vs
    cr
    @8
    c1
    cN
    cfz
    co
    #
    vk
    cv
    #
    @1
    cmul
    co
    #
    ccos
    cfv
    #
    vk
    csu
    #
    caddc
    co
    #
    cpi
    cdiv
    co
    #
    cmpt
    @17
    dirkertrigeq.h
    wph
    vs
    cr
    @25
    @16
    wph
    @1
    cr
    wcel
    #
    wa
    #
    @4
    @25
    @16
    wceq
    @27
    @4
    wa
    #
    @7
    @6
    c2
    cdiv
    co
    #
    cpi
    cdiv
    co
    #
    @16
    @25
    wph
    @7
    @30
    wceq
    @26
    @4
    wph
    @30
    @7
    wph
    @6
    c2
    cpi
    wph
    @5
    cc
    wcel
    @6
    cc
    wcel
    wph
    c2
    cN
    wph
    2cnd
    #
    wph
    cN
    dirkertrigeq.n
    nncnd
    #
    mulcld
    @5
    peano2cn
    syl
    @31
    cpi
    cc
    wcel
    #
    wph
    picn
    a1i
    c2
    cc0
    wne
    wph
    2ne0
    a1i
    #
    cpi
    cc0
    wne
    #
    wph
    cpi
    pire
    pipos
    gt0ne0ii
    #
    a1i
    divdiv1d
    eqcomd
    ad2antrr
    @4
    @16
    @7
    wceq
    @27
    @4
    @7
    @15
    iftrue
    adantl
    @28
    @24
    @29
    cpi
    cdiv
    @28
    @24
    @8
    cN
    caddc
    co
    #
    @29
    @28
    @23
    cN
    @8
    caddc
    @28
    @23
    @19
    c1
    vk
    csu
    #
    @19
    chash
    cfv
    #
    c1
    cmul
    co
    #
    cN
    @28
    @19
    @22
    c1
    vk
    @26
    @4
    @22
    c1
    wceq
    #
    vk
    @19
    wral
    wph
    @26
    @4
    wa
    #
    @41
    vk
    @19
    @42
    @20
    @19
    wcel
    #
    wa
    #
    @41
    @21
    @2
    cdiv
    co
    #
    cz
    wcel
    #
    @44
    @45
    @20
    @1
    @2
    cdiv
    co
    #
    cmul
    co
    cz
    @44
    @20
    @1
    @2
    @43
    @20
    cc
    wcel
    #
    @42
    @43
    @20
    @20
    c1
    cN
    elfzelz
    #
    zcnd
    #
    adantl
    @26
    @1
    cc
    wcel
    #
    @4
    @43
    @1
    recn
    #
    ad2antrr
    @2
    cc
    wcel
    #
    @44
    c2
    cpi
    2cn
    picn
    mulcli
    #
    a1i
    @2
    cc0
    wne
    @44
    c2
    cpi
    2cn
    picn
    2ne0
    @36
    mulne0i
    a1i
    divassd
    @44
    @20
    @47
    @43
    @20
    cz
    wcel
    @42
    @49
    adantl
    @42
    @47
    cz
    wcel
    #
    @43
    @42
    @4
    @55
    @26
    @4
    simpr
    @42
    @26
    @2
    crp
    wcel
    #
    @4
    @55
    wb
    @26
    @4
    simpl
    c2
    crp
    wcel
    cpi
    crp
    wcel
    #
    @56
    2rp
    pirp
    c2
    cpi
    rpmulcl
    mp2an
    #
    @1
    @2
    mod0
    sylancl
    mpbid
    adantr
    zmulcld
    eqeltrd
    @26
    @43
    @41
    @46
    wb
    #
    @4
    @26
    @43
    wa
    #
    @21
    cc
    wcel
    @59
    @60
    @20
    @1
    @43
    @48
    @26
    @50
    adantl
    @26
    @51
    @43
    @52
    adantr
    mulcld
    @21
    coseq1
    syl
    adantlr
    mpbird
    ralrimiva
    adantll
    sumeq2d
    @28
    @19
    cfn
    wcel
    c1
    cc
    wcel
    @38
    @40
    wceq
    @28
    c1
    cN
    fzfid
    @28
    1cnd
    @19
    c1
    vk
    fsumconst
    syl2anc
    wph
    @40
    cN
    wceq
    @26
    @4
    wph
    @40
    cN
    c1
    cmul
    co
    cN
    wph
    @39
    cN
    c1
    cmul
    wph
    cN
    cn0
    wcel
    @39
    cN
    wceq
    wph
    cN
    dirkertrigeq.n
    nnnn0d
    cN
    hashfz1
    syl
    oveq1d
    wph
    cN
    @32
    mulid1d
    eqtrd
    ad2antrr
    3eqtrd
    oveq2d
    wph
    @37
    @29
    wceq
    @26
    @4
    wph
    @37
    @8
    cN
    c1
    cdiv
    co
    #
    caddc
    co
    c1
    c1
    cmul
    co
    #
    cN
    c2
    cmul
    co
    #
    caddc
    co
    #
    c2
    c1
    cmul
    co
    #
    cdiv
    co
    @29
    wph
    cN
    @61
    @8
    caddc
    wph
    @61
    cN
    wph
    cN
    @32
    div1d
    eqcomd
    oveq2d
    wph
    c1
    c2
    cN
    c1
    wph
    1cnd
    #
    @31
    @32
    @66
    @34
    c1
    cc0
    wne
    wph
    ax-1ne0
    a1i
    divadddivd
    wph
    @64
    @6
    @65
    c2
    cdiv
    wph
    @64
    @63
    @62
    caddc
    co
    @6
    wph
    @62
    @63
    wph
    c1
    c1
    @66
    @66
    mulcld
    wph
    cN
    c2
    @32
    @31
    mulcld
    addcomd
    wph
    @63
    @5
    @62
    c1
    caddc
    wph
    cN
    c2
    @32
    @31
    mulcomd
    wph
    c1
    @66
    mulid1d
    oveq12d
    eqtrd
    wph
    c2
    @31
    mulid1d
    oveq12d
    3eqtrd
    ad2antrr
    eqtrd
    oveq1d
    3eqtr4rd
    @27
    @4
    wn
    #
    wa
    #
    @16
    @15
    @25
    @67
    @16
    @15
    wceq
    @27
    @4
    @7
    @15
    iffalse
    adantl
    @68
    @1
    cpi
    cmo
    co
    cc0
    wceq
    #
    @15
    @25
    wceq
    #
    @68
    @69
    wa
    #
    @25
    @8
    @19
    @20
    c2
    @1
    cpi
    cdiv
    co
    #
    c2
    cdiv
    co
    #
    cfl
    cfv
    #
    cmul
    co
    c1
    caddc
    co
    #
    cpi
    cmul
    co
    #
    cmul
    co
    #
    ccos
    cfv
    #
    vk
    csu
    #
    caddc
    co
    #
    cpi
    cdiv
    co
    #
    @9
    @76
    cmul
    co
    #
    csin
    cfv
    #
    @2
    @76
    c2
    cdiv
    co
    #
    csin
    cfv
    #
    cmul
    co
    #
    cdiv
    co
    #
    @15
    @26
    @67
    @69
    @25
    @81
    wceq
    wph
    @26
    @67
    wa
    #
    @69
    wa
    #
    @24
    @80
    cpi
    cdiv
    @89
    @23
    @79
    @8
    caddc
    @89
    @19
    @22
    @78
    vk
    @89
    @21
    @77
    ccos
    @89
    @1
    @76
    @20
    cmul
    @89
    @1
    @72
    cpi
    cmul
    co
    #
    @76
    @26
    @1
    @90
    wceq
    @67
    @69
    @26
    @90
    @1
    @26
    @1
    cpi
    @52
    @33
    @26
    picn
    a1i
    #
    @35
    @26
    @36
    a1i
    #
    divcan1d
    #
    eqcomd
    ad2antrr
    @89
    @72
    @75
    cpi
    cmul
    @89
    @72
    cz
    wcel
    #
    @72
    c2
    cmo
    co
    #
    cc0
    wne
    #
    @72
    @75
    wceq
    #
    @26
    @69
    @94
    @67
    @26
    @69
    wa
    #
    @69
    @94
    @26
    @69
    simpr
    @98
    @26
    @57
    @69
    @94
    wb
    #
    @26
    @69
    simpl
    pirp
    @1
    cpi
    mod0
    #
    sylancl
    mpbid
    adantlr
    @88
    @96
    @69
    @88
    @95
    c1
    cpi
    cdiv
    co
    #
    @3
    cmul
    co
    #
    cc0
    @26
    @95
    @102
    wceq
    @67
    @26
    @102
    @101
    @1
    cmul
    co
    #
    @101
    @2
    cmul
    co
    #
    cmo
    co
    #
    @95
    @101
    crp
    wcel
    #
    @26
    @56
    @102
    @105
    wceq
    @57
    @106
    pirp
    cpi
    rpreccl
    ax-mp
    @58
    @101
    @1
    @2
    moddi
    mp3an13
    @26
    @103
    @72
    @104
    c2
    cmo
    @26
    @72
    @103
    @26
    @1
    cpi
    @52
    @91
    @92
    divrec2d
    eqcomd
    @26
    @104
    @2
    @101
    cmul
    co
    c2
    cpi
    @101
    cmul
    co
    #
    cmul
    co
    #
    c2
    @26
    @101
    @2
    @26
    cpi
    @91
    @92
    reccld
    #
    @53
    @26
    @54
    a1i
    mulcomd
    @26
    c2
    cpi
    @101
    @26
    2cnd
    #
    @91
    @109
    mulassd
    @26
    @108
    @65
    c2
    @107
    c1
    c2
    cmul
    cpi
    picn
    @36
    recidi
    oveq2i
    @26
    c2
    @110
    mulid1d
    syl5eq
    3eqtrd
    oveq12d
    eqtr2d
    adantr
    @88
    @101
    @3
    @26
    @101
    cc
    wcel
    @67
    @109
    adantr
    @26
    @3
    cc
    wcel
    @67
    @26
    @3
    @26
    @1
    @2
    @26
    id
    #
    @56
    @26
    @58
    a1i
    modcld
    recnd
    adantr
    @101
    cc0
    wne
    @88
    c1
    cpi
    ax-1cn
    picn
    ax-1ne0
    @36
    divne0i
    a1i
    @67
    @3
    cc0
    wne
    @26
    @3
    cc0
    neqne
    adantl
    mulne0d
    eqnetrd
    adantr
    @72
    oddfl
    syl2anc
    #
    oveq1d
    eqtrd
    oveq2d
    fveq2d
    sumeq2sdv
    oveq2d
    oveq1d
    adantlll
    @27
    @69
    @81
    @87
    wceq
    @67
    @27
    @69
    wa
    @76
    vk
    @74
    cN
    wph
    @18
    @26
    @69
    dirkertrigeq.n
    ad2antrr
    @26
    @74
    cz
    wcel
    wph
    @69
    @26
    @73
    @26
    @72
    @26
    @1
    cpi
    @111
    cpi
    cr
    wcel
    @26
    pire
    a1i
    @92
    redivcld
    rehalfcld
    flcld
    ad2antlr
    @76
    eqid
    dirkertrigeqlem3
    adantlr
    @71
    @87
    @9
    @90
    cmul
    co
    #
    csin
    cfv
    #
    @2
    @90
    c2
    cdiv
    co
    #
    csin
    cfv
    #
    cmul
    co
    #
    cdiv
    co
    #
    @15
    @71
    @83
    @114
    @86
    @117
    cdiv
    @71
    @82
    @113
    csin
    @71
    @76
    @90
    @9
    cmul
    @71
    @75
    @72
    cpi
    cmul
    @71
    @72
    @75
    @26
    @67
    @69
    @97
    wph
    @112
    adantlll
    eqcomd
    oveq1d
    #
    oveq2d
    fveq2d
    @71
    @85
    @116
    @2
    cmul
    @71
    @84
    @115
    csin
    @71
    @76
    @90
    c2
    cdiv
    @119
    oveq1d
    fveq2d
    oveq2d
    oveq12d
    @27
    @118
    @15
    wceq
    #
    @67
    @69
    @26
    @120
    wph
    @26
    @114
    @11
    @117
    @14
    cdiv
    @26
    @113
    @10
    csin
    @26
    @90
    @1
    @9
    cmul
    @93
    oveq2d
    fveq2d
    @26
    @116
    @13
    @2
    cmul
    @26
    @115
    @12
    csin
    @26
    @90
    @1
    c2
    cdiv
    @93
    oveq1d
    fveq2d
    oveq2d
    oveq12d
    adantl
    ad2antrr
    eqtrd
    3eqtrrd
    @27
    @69
    wn
    #
    @70
    @67
    @27
    @121
    wa
    #
    @25
    @15
    @122
    @1
    vk
    cN
    wph
    @26
    @121
    simplr
    #
    @122
    @1
    csin
    cfv
    #
    cc0
    @122
    @124
    cc0
    wceq
    #
    @94
    @122
    @69
    @94
    @27
    @121
    simpr
    @122
    @26
    @57
    @99
    @123
    pirp
    @100
    sylancl
    mtbid
    @122
    @51
    @125
    @94
    wb
    @122
    @1
    @123
    recnd
    @1
    sineq0
    syl
    mtbird
    neqned
    wph
    @18
    @26
    @121
    dirkertrigeq.n
    ad2antrr
    dirkertrigeqlem2
    eqcomd
    adantlr
    pm2.61dan
    eqtr2d
    pm2.61dan
    mpteq2dva
    syl5req
    3eqtrd
end
