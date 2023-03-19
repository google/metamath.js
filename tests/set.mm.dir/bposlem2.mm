include "c2.mm"
include "cmul.mm"
include "co.mm"
include "cbc.mm"
include "cpc.mm"
include "c1.mm"
include "cfz.mm"
include "cv.mm"
include "cexp.mm"
include "cdiv.mm"
include "cfl.mm"
include "cfv.mm"
include "cmin.mm"
include "csu.mm"
include "cc0.mm"
include "cn.mm"
include "wcel.mm"
include "cprime.mm"
include "wceq.mm"
include "pcbcctr.mm"
include "syl2anc.mm"
include "cuz.mm"
include "wo.mm"
include "elfznn.mm"
include "elnn1uz2.mm"
include "sylib.mm"
include "wa.mm"
include "oveq2.mm"
include "prmnn.mm"
include "syl.mm"
include "nncnd.mm"
include "exp1d.mm"
include "sylan9eqr.mm"
include "oveq2d.mm"
include "fveq2d.mm"
include "cle.mm"
include "wbr.mm"
include "caddc.mm"
include "clt.mm"
include "2t1e2.mm"
include "mulid2d.mm"
include "eqbrtrd.mm"
include "cr.mm"
include "wb.mm"
include "1red.mm"
include "nnred.mm"
include "nngt0d.mm"
include "lemuldiv.mm"
include "syl112anc.mm"
include "mpbid.mm"
include "nndivred.mm"
include "1re.mm"
include "2re.mm"
include "2pos.mm"
include "pm3.2i.mm"
include "lemul2.mm"
include "mp3an13.mm"
include "syl5eqbrr.mm"
include "2cnd.mm"
include "nnne0d.mm"
include "divassd.mm"
include "breqtrrd.mm"
include "c3.mm"
include "2nn.mm"
include "nnmulcl.mm"
include "sylancr.mm"
include "3re.mm"
include "3pos.mm"
include "ltdiv23.mm"
include "mp3an2.mm"
include "syl12anc.mm"
include "df-3.mm"
include "syl6breq.mm"
include "cz.mm"
include "2z.mm"
include "flbi.mm"
include "sylancl.mm"
include "mpbir2and.mm"
include "adantr.mm"
include "eqtrd.mm"
include "c4.mm"
include "remulcl.mm"
include "a1i.mm"
include "4re.mm"
include "eqbrtrrd.mm"
include "3lt4.mm"
include "lttrd.mm"
include "2t2e4.mm"
include "syl6breqr.mm"
include "ltmul2.mm"
include "mp3an23.mm"
include "mpbird.mm"
include "df-2.mm"
include "1z.mm"
include "syl6eq.mm"
include "oveq12d.mm"
include "2cn.mm"
include "subidi.mm"
include "crp.mm"
include "nnrpd.mm"
include "cn0.mm"
include "eluzge2nn0.mm"
include "nnexpcl.mm"
include "syl2an.mm"
include "rpdivcld.mm"
include "rpge0d.mm"
include "ltdivmul.mm"
include "mp3an3.mm"
include "remulcld.mm"
include "nnltp1le.mm"
include "syl5eqbr.mm"
include "lemul1.mm"
include "mp3an1.mm"
include "sqvald.mm"
include "nnge1d.mm"
include "simpr.mm"
include "leexp2ad.mm"
include "letrd.mm"
include "ltletrd.mm"
include "mulid1d.mm"
include "ltdivmuld.mm"
include "1e0p1.mm"
include "rpred.mm"
include "0z.mm"
include "ltaddrpd.mm"
include "2timesd.mm"
include "2t0e0.mm"
include "0m0e0.mm"
include "jaodan.mm"
include "sylan2.mm"
include "sumeq2dv.mm"
include "cfn.mm"
include "fzfid.mm"
include "wss.mm"
include "sumz.mm"
include "olcs.mm"

theorem bposlem2
  let wph: wff ph
  let cP: class P
  let cN: class N
  let vk: setvar k
  assume bposlem2.1: |- ( ph -> N e. NN )
  assume bposlem2.2: |- ( ph -> P e. Prime )
  assume bposlem2.3: |- ( ph -> 2 < P )
  assume bposlem2.4: |- ( ph -> ( ( 2 x. N ) / 3 ) < P )
  assume bposlem2.5: |- ( ph -> P <_ N )


  assert |- ( ph -> ( P pCnt ( ( 2 x. N ) _C N ) ) = 0 )

  proof
    wph
    cP
    c2
    cN
    cmul
    co
    #
    cN
    cbc
    co
    cpc
    co
    #
    c1
    @0
    cfz
    co
    #
    @0
    cP
    vk
    cv
    #
    cexp
    co
    #
    cdiv
    co
    #
    cfl
    cfv
    #
    c2
    cN
    @4
    cdiv
    co
    #
    cfl
    cfv
    #
    cmul
    co
    #
    cmin
    co
    #
    vk
    csu
    #
    cc0
    wph
    cN
    cn
    wcel
    #
    cP
    cprime
    wcel
    #
    @1
    @11
    wceq
    bposlem2.1
    bposlem2.2
    cP
    vk
    cN
    pcbcctr
    syl2anc
    wph
    @11
    @2
    cc0
    vk
    csu
    #
    cc0
    wph
    @2
    @10
    cc0
    vk
    @3
    @2
    wcel
    #
    wph
    @3
    c1
    wceq
    #
    @3
    c2
    cuz
    cfv
    wcel
    #
    wo
    #
    @10
    cc0
    wceq
    #
    @15
    @3
    cn
    wcel
    @18
    @3
    @0
    elfznn
    @3
    elnn1uz2
    sylib
    wph
    @16
    @19
    @17
    wph
    @16
    wa
    #
    @10
    c2
    c2
    cmin
    co
    cc0
    @20
    @6
    c2
    @9
    c2
    cmin
    @20
    @6
    @0
    cP
    cdiv
    co
    #
    cfl
    cfv
    #
    c2
    @20
    @5
    @21
    cfl
    @20
    @4
    cP
    @0
    cdiv
    @16
    wph
    @4
    cP
    c1
    cexp
    co
    cP
    @3
    c1
    cP
    cexp
    oveq2
    wph
    cP
    wph
    cP
    wph
    @13
    cP
    cn
    wcel
    #
    bposlem2.2
    cP
    prmnn
    syl
    #
    nncnd
    #
    exp1d
    sylan9eqr
    #
    oveq2d
    fveq2d
    wph
    @22
    c2
    wceq
    #
    @16
    wph
    @27
    c2
    @21
    cle
    wbr
    #
    @21
    c2
    c1
    caddc
    co
    #
    clt
    wbr
    #
    wph
    c2
    c2
    cN
    cP
    cdiv
    co
    #
    cmul
    co
    #
    @21
    cle
    wph
    c2
    c2
    c1
    cmul
    co
    #
    @32
    cle
    2t1e2
    wph
    c1
    @31
    cle
    wbr
    #
    @33
    @32
    cle
    wbr
    #
    wph
    c1
    cP
    cmul
    co
    #
    cN
    cle
    wbr
    #
    @34
    wph
    @36
    cP
    cN
    cle
    wph
    cP
    @25
    mulid2d
    bposlem2.5
    eqbrtrd
    wph
    c1
    cr
    wcel
    #
    cN
    cr
    wcel
    #
    cP
    cr
    wcel
    #
    cc0
    cP
    clt
    wbr
    #
    @37
    @34
    wb
    wph
    1red
    wph
    cN
    bposlem2.1
    nnred
    #
    wph
    cP
    @24
    nnred
    #
    wph
    cP
    @24
    nngt0d
    #
    c1
    cN
    cP
    lemuldiv
    syl112anc
    mpbid
    #
    wph
    @31
    cr
    wcel
    #
    @34
    @35
    wb
    #
    wph
    cN
    cP
    @42
    @24
    nndivred
    #
    @38
    @46
    c2
    cr
    wcel
    #
    cc0
    c2
    clt
    wbr
    #
    wa
    #
    @47
    1re
    @49
    @50
    2re
    2pos
    pm3.2i
    #
    c1
    @31
    c2
    lemul2
    mp3an13
    syl
    mpbid
    syl5eqbrr
    wph
    c2
    cN
    cP
    wph
    2cnd
    wph
    cN
    bposlem2.1
    nncnd
    #
    @25
    wph
    cP
    @24
    nnne0d
    divassd
    #
    breqtrrd
    wph
    @21
    c3
    @29
    clt
    wph
    @0
    c3
    cdiv
    co
    cP
    clt
    wbr
    #
    @21
    c3
    clt
    wbr
    #
    bposlem2.4
    wph
    @0
    cr
    wcel
    #
    @40
    @41
    @55
    @56
    wb
    #
    wph
    @0
    wph
    c2
    cn
    wcel
    #
    @12
    @0
    cn
    wcel
    2nn
    bposlem2.1
    c2
    cN
    nnmulcl
    sylancr
    #
    nnred
    #
    @43
    @44
    @57
    c3
    cr
    wcel
    #
    cc0
    c3
    clt
    wbr
    #
    wa
    #
    @40
    @41
    wa
    #
    @58
    @62
    @63
    3re
    3pos
    pm3.2i
    #
    @0
    c3
    cP
    ltdiv23
    mp3an2
    syl12anc
    mpbid
    #
    df-3
    syl6breq
    wph
    @21
    cr
    wcel
    c2
    cz
    wcel
    @27
    @28
    @30
    wa
    wb
    wph
    @0
    cP
    @61
    @24
    nndivred
    2z
    @21
    c2
    flbi
    sylancl
    mpbir2and
    adantr
    eqtrd
    @20
    @9
    @33
    c2
    @20
    @8
    c1
    c2
    cmul
    @20
    @8
    @31
    cfl
    cfv
    #
    c1
    @20
    @7
    @31
    cfl
    @20
    @4
    cP
    cN
    cdiv
    @26
    oveq2d
    fveq2d
    wph
    @68
    c1
    wceq
    #
    @16
    wph
    @69
    @34
    @31
    c1
    c1
    caddc
    co
    #
    clt
    wbr
    #
    @45
    wph
    @31
    c2
    @70
    clt
    wph
    @31
    c2
    clt
    wbr
    #
    @32
    c2
    c2
    cmul
    co
    #
    clt
    wbr
    #
    wph
    @32
    c4
    @73
    clt
    wph
    @32
    c3
    c4
    wph
    @49
    @46
    @32
    cr
    wcel
    2re
    @48
    c2
    @31
    remulcl
    sylancr
    @62
    wph
    3re
    a1i
    c4
    cr
    wcel
    wph
    4re
    a1i
    wph
    @21
    @32
    c3
    clt
    @54
    @67
    eqbrtrrd
    c3
    c4
    clt
    wbr
    wph
    3lt4
    a1i
    lttrd
    2t2e4
    syl6breqr
    wph
    @46
    @72
    @74
    wb
    #
    @48
    @46
    @49
    @51
    @75
    2re
    @52
    @31
    c2
    c2
    ltmul2
    mp3an23
    syl
    mpbird
    df-2
    syl6breq
    wph
    @46
    c1
    cz
    wcel
    @69
    @34
    @71
    wa
    wb
    @48
    1z
    @31
    c1
    flbi
    sylancl
    mpbir2and
    adantr
    eqtrd
    oveq2d
    2t1e2
    syl6eq
    oveq12d
    c2
    2cn
    subidi
    syl6eq
    wph
    @17
    wa
    #
    @10
    cc0
    cc0
    cmin
    co
    cc0
    @76
    @6
    cc0
    @9
    cc0
    cmin
    @76
    @6
    cc0
    wceq
    #
    cc0
    @5
    cle
    wbr
    #
    @5
    cc0
    c1
    caddc
    co
    #
    clt
    wbr
    #
    @76
    @5
    @76
    @0
    @4
    wph
    @0
    crp
    wcel
    @17
    wph
    @0
    @60
    nnrpd
    adantr
    @76
    @4
    wph
    @23
    @3
    cn0
    wcel
    @4
    cn
    wcel
    @17
    @24
    @3
    eluzge2nn0
    cP
    @3
    nnexpcl
    syl2an
    #
    nnrpd
    #
    rpdivcld
    #
    rpge0d
    @76
    @5
    c1
    @79
    clt
    @76
    @5
    c1
    clt
    wbr
    @0
    @4
    c1
    cmul
    co
    #
    clt
    wbr
    @76
    @0
    @4
    @84
    clt
    @76
    @0
    c3
    cP
    cmul
    co
    #
    @4
    wph
    @57
    @17
    @61
    adantr
    #
    wph
    @85
    cr
    wcel
    #
    @17
    wph
    @62
    @40
    @87
    3re
    @43
    c3
    cP
    remulcl
    sylancr
    adantr
    #
    @76
    @4
    @81
    nnred
    #
    wph
    @0
    @85
    clt
    wbr
    #
    @17
    wph
    @55
    @90
    bposlem2.4
    wph
    @57
    @40
    @55
    @90
    wb
    #
    @61
    @43
    @57
    @40
    @64
    @91
    @66
    @0
    cP
    c3
    ltdivmul
    mp3an3
    syl2anc
    mpbid
    adantr
    @76
    @85
    cP
    cP
    cmul
    co
    #
    @4
    @88
    wph
    @92
    cr
    wcel
    @17
    wph
    cP
    cP
    @43
    @43
    remulcld
    adantr
    @89
    wph
    @85
    @92
    cle
    wbr
    #
    @17
    wph
    c3
    cP
    cle
    wbr
    #
    @93
    wph
    c3
    @29
    cP
    cle
    df-3
    wph
    c2
    cP
    clt
    wbr
    #
    @29
    cP
    cle
    wbr
    #
    bposlem2.3
    wph
    @59
    @23
    @95
    @96
    wb
    2nn
    @24
    c2
    cP
    nnltp1le
    sylancr
    mpbid
    syl5eqbr
    wph
    @40
    @40
    @41
    @94
    @93
    wb
    #
    @43
    @43
    @44
    @62
    @40
    @65
    @97
    3re
    c3
    cP
    cP
    lemul1
    mp3an1
    syl12anc
    mpbid
    adantr
    @76
    cP
    c2
    cexp
    co
    #
    @92
    @4
    cle
    wph
    @98
    @92
    wceq
    @17
    wph
    cP
    @25
    sqvald
    adantr
    @76
    cP
    c2
    @3
    wph
    @40
    @17
    @43
    adantr
    wph
    c1
    cP
    cle
    wbr
    @17
    wph
    cP
    @24
    nnge1d
    adantr
    wph
    @17
    simpr
    leexp2ad
    eqbrtrrd
    letrd
    ltletrd
    #
    @76
    @4
    @76
    @4
    @81
    nncnd
    mulid1d
    #
    breqtrrd
    @76
    @0
    c1
    @4
    @86
    @76
    1red
    #
    @82
    ltdivmuld
    mpbird
    1e0p1
    syl6breq
    @76
    @5
    cr
    wcel
    cc0
    cz
    wcel
    #
    @77
    @78
    @80
    wa
    wb
    @76
    @5
    @83
    rpred
    0z
    @5
    cc0
    flbi
    sylancl
    mpbir2and
    @76
    @9
    c2
    cc0
    cmul
    co
    cc0
    @76
    @8
    cc0
    c2
    cmul
    @76
    @8
    cc0
    wceq
    #
    cc0
    @7
    cle
    wbr
    #
    @7
    @79
    clt
    wbr
    #
    @76
    @7
    @76
    cN
    @4
    wph
    cN
    crp
    wcel
    @17
    wph
    cN
    bposlem2.1
    nnrpd
    #
    adantr
    @82
    rpdivcld
    #
    rpge0d
    @76
    @7
    c1
    @79
    clt
    @76
    @7
    c1
    clt
    wbr
    cN
    @84
    clt
    wbr
    @76
    cN
    @4
    @84
    clt
    @76
    cN
    @0
    @4
    wph
    @39
    @17
    @42
    adantr
    #
    @86
    @89
    wph
    cN
    @0
    clt
    wbr
    @17
    wph
    cN
    cN
    cN
    caddc
    co
    @0
    clt
    wph
    cN
    cN
    @42
    @106
    ltaddrpd
    wph
    cN
    @53
    2timesd
    breqtrrd
    adantr
    @99
    lttrd
    @100
    breqtrrd
    @76
    cN
    c1
    @4
    @108
    @101
    @82
    ltdivmuld
    mpbird
    1e0p1
    syl6breq
    @76
    @7
    cr
    wcel
    @102
    @103
    @104
    @105
    wa
    wb
    @76
    @7
    @107
    rpred
    0z
    @7
    cc0
    flbi
    sylancl
    mpbir2and
    oveq2d
    2t0e0
    syl6eq
    oveq12d
    0m0e0
    syl6eq
    jaodan
    sylan2
    sumeq2dv
    wph
    @2
    cfn
    wcel
    #
    @14
    cc0
    wceq
    #
    wph
    c1
    @0
    fzfid
    @2
    c1
    cuz
    cfv
    wss
    @109
    @110
    @2
    vk
    c1
    sumz
    olcs
    syl
    eqtrd
    eqtrd
end
