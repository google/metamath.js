include "c4.mm"
include "cuz.mm"
include "cfv.mm"
include "wcel.mm"
include "cexp.mm"
include "co.mm"
include "cdiv.mm"
include "clog.mm"
include "c2.mm"
include "cmul.mm"
include "cbc.mm"
include "cppi.mm"
include "cn.mm"
include "cn0.mm"
include "4nn.mm"
include "eluznn.mm"
include "mpan.mm"
include "nnnn0d.mm"
include "nnexpcl.mm"
include "sylancr.mm"
include "nnrpd.mm"
include "rpdivcld.mm"
include "relogcld.mm"
include "cc0.mm"
include "cfz.mm"
include "fzctr.mm"
include "syl.mm"
include "bccl2.mm"
include "cr.mm"
include "cz.mm"
include "2z.mm"
include "eluzelz.mm"
include "zmulcl.mm"
include "zred.mm"
include "ppicl.mm"
include "nn0red.mm"
include "2nn.mm"
include "nnmulcl.mm"
include "remulcld.mm"
include "clt.mm"
include "wbr.mm"
include "bclbnd.mm"
include "crp.mm"
include "wb.mm"
include "logltb.mm"
include "syl2anc.mm"
include "mpbid.mm"
include "cle.mm"
include "cif.mm"
include "ifcld.mm"
include "syl5eqel.mm"
include "nnred.mm"
include "c1.mm"
include "cprime.mm"
include "cin.mm"
include "cv.mm"
include "cpc.mm"
include "csu.mm"
include "cfn.mm"
include "wss.mm"
include "fzfid.mm"
include "inss1.mm"
include "ssfi.mm"
include "sylancl.mm"
include "nnzd.mm"
include "min2.mm"
include "syl5eqbr.mm"
include "eluz2.mm"
include "syl3anbrc.mm"
include "fzss2.mm"
include "ssrin.mm"
include "sselda.mm"
include "wa.mm"
include "simpr.mm"
include "sseldi.mm"
include "elfznn.mm"
include "inss2.mm"
include "adantr.mm"
include "pccld.mm"
include "nnexpcld.mm"
include "syldan.mm"
include "ce.mm"
include "elin.mm"
include "simprbi.mm"
include "bposlem1.mm"
include "syl2an.mm"
include "reeflogd.mm"
include "3brtr4d.mm"
include "efle.mm"
include "mpbird.mm"
include "fsumle.mm"
include "cc.mm"
include "recnd.mm"
include "cdif.mm"
include "wn.mm"
include "wceq.mm"
include "eldifn.mm"
include "adantl.mm"
include "eldifad.mm"
include "adantrr.mm"
include "nncnd.mm"
include "exp1d.mm"
include "nnge1d.mm"
include "simprr.mm"
include "nnuz.mm"
include "syl6eleq.mm"
include "leexp2ad.mm"
include "eqbrtrrd.mm"
include "letrd.mm"
include "elfzle2.mm"
include "lemin.mm"
include "syl3anc.mm"
include "mpbir2and.mm"
include "syl6breqr.mm"
include "fznn.mm"
include "elind.mm"
include "expr.mm"
include "mtod.mm"
include "wo.mm"
include "elnn0.mm"
include "sylib.mm"
include "ord.mm"
include "mpd.mm"
include "oveq2d.mm"
include "exp0d.mm"
include "eqtrd.mm"
include "fveq2d.mm"
include "log1.mm"
include "syl6eq.mm"
include "fsumss.mm"
include "nn0zd.mm"
include "relogexp.mm"
include "sumeq2dv.mm"
include "pclogsum.mm"
include "3eqtrd.mm"
include "chash.mm"
include "fsumconst.mm"
include "2eluzge1.mm"
include "ppival2g.mm"
include "oveq1d.mm"
include "eqtr4d.mm"
include "3brtr3d.mm"
include "min1.mm"
include "ppiwordi.mm"
include "1red.mm"
include "2re.mm"
include "a1i.mm"
include "1lt2.mm"
include "2t1e2.mm"
include "eluzelre.mm"
include "2pos.mm"
include "pm3.2i.mm"
include "lemul2.mm"
include "syl5eqbrr.mm"
include "ltletrd.mm"
include "rplogcld.mm"
include "lemul1d.mm"

theorem chebbnd1lem1
  let cK: class K
  let cN: class N
  let vk: setvar k
  assume chebbnd1lem1.1: |- K = if ( ( 2 x. N ) <_ ( ( 2 x. N ) _C N ) , ( 2 x. N ) , ( ( 2 x. N ) _C N ) )


  assert |- ( N e. ( ZZ>= ` 4 ) -> ( log ` ( ( 4 ^ N ) / N ) ) < ( ( ppi ` ( 2 x. N ) ) x. ( log ` ( 2 x. N ) ) ) )

  proof
    cN
    c4
    cuz
    cfv
    wcel
    #
    c4
    cN
    cexp
    co
    #
    cN
    cdiv
    co
    #
    clog
    cfv
    #
    c2
    cN
    cmul
    co
    #
    cN
    cbc
    co
    #
    clog
    cfv
    #
    @4
    cppi
    cfv
    #
    @4
    clog
    cfv
    #
    cmul
    co
    #
    @0
    @2
    @0
    @1
    cN
    @0
    @1
    @0
    c4
    cn
    wcel
    #
    cN
    cn0
    wcel
    #
    @1
    cn
    wcel
    4nn
    @0
    cN
    @10
    @0
    cN
    cn
    wcel
    #
    4nn
    cN
    c4
    eluznn
    mpan
    #
    nnnn0d
    #
    c4
    cN
    nnexpcl
    sylancr
    nnrpd
    @0
    cN
    @13
    nnrpd
    rpdivcld
    #
    relogcld
    @0
    @5
    @0
    @5
    @0
    cN
    cc0
    @4
    cfz
    co
    wcel
    #
    @5
    cn
    wcel
    #
    @0
    @11
    @16
    @14
    cN
    fzctr
    syl
    cN
    @4
    bccl2
    syl
    #
    nnrpd
    #
    relogcld
    #
    @0
    @7
    @8
    @0
    @7
    @0
    @4
    cr
    wcel
    #
    @7
    cn0
    wcel
    @0
    @4
    @0
    c2
    cz
    wcel
    cN
    cz
    wcel
    @4
    cz
    wcel
    2z
    c4
    cN
    eluzelz
    c2
    cN
    zmulcl
    sylancr
    zred
    #
    @4
    ppicl
    syl
    nn0red
    #
    @0
    @4
    @0
    @4
    @0
    c2
    cn
    wcel
    @12
    @4
    cn
    wcel
    2nn
    @13
    c2
    cN
    nnmulcl
    sylancr
    #
    nnrpd
    #
    relogcld
    #
    remulcld
    #
    @0
    @2
    @5
    clt
    wbr
    #
    @3
    @6
    clt
    wbr
    #
    cN
    bclbnd
    @0
    @2
    crp
    wcel
    @5
    crp
    wcel
    @28
    @29
    wb
    @15
    @19
    @2
    @5
    logltb
    syl2anc
    mpbid
    @0
    @6
    cK
    cppi
    cfv
    #
    @8
    cmul
    co
    #
    @9
    @20
    @0
    @30
    @8
    @0
    @30
    @0
    cK
    cr
    wcel
    #
    @30
    cn0
    wcel
    @0
    cK
    @0
    cK
    @4
    @5
    cle
    wbr
    #
    @4
    @5
    cif
    #
    cn
    chebbnd1lem1.1
    @0
    @33
    @4
    @5
    cn
    @24
    @18
    ifcld
    syl5eqel
    #
    nnred
    #
    cK
    ppicl
    syl
    nn0red
    #
    @26
    remulcld
    @27
    @0
    c1
    cK
    cfz
    co
    #
    cprime
    cin
    #
    vk
    cv
    #
    @40
    @5
    cpc
    co
    #
    cexp
    co
    #
    clog
    cfv
    #
    vk
    csu
    #
    @39
    @8
    vk
    csu
    #
    @6
    @31
    cle
    @0
    @39
    @43
    @8
    vk
    @0
    @38
    cfn
    wcel
    @39
    @38
    wss
    @39
    cfn
    wcel
    #
    @0
    c1
    cK
    fzfid
    @38
    cprime
    inss1
    @38
    @39
    ssfi
    sylancl
    #
    @0
    @40
    @39
    wcel
    #
    @40
    c1
    @5
    cfz
    co
    #
    cprime
    cin
    #
    wcel
    #
    @43
    cr
    wcel
    #
    @0
    @39
    @50
    @40
    @0
    @38
    @49
    wss
    #
    @39
    @50
    wss
    @0
    @5
    cK
    cuz
    cfv
    wcel
    #
    @53
    @0
    cK
    cz
    wcel
    #
    @5
    cz
    wcel
    cK
    @5
    cle
    wbr
    @54
    @0
    cK
    @35
    nnzd
    #
    @0
    @5
    @18
    nnzd
    @0
    cK
    @34
    @5
    cle
    chebbnd1lem1.1
    @0
    @21
    @5
    cr
    wcel
    #
    @34
    @5
    cle
    wbr
    @22
    @0
    @5
    @18
    nnred
    #
    @4
    @5
    min2
    syl2anc
    syl5eqbr
    cK
    @5
    eluz2
    syl3anbrc
    cK
    c1
    @5
    fzss2
    syl
    @38
    @49
    cprime
    ssrin
    syl
    #
    sselda
    #
    @0
    @51
    wa
    #
    @42
    @61
    @42
    @61
    @40
    @41
    @61
    @40
    @49
    wcel
    #
    @40
    cn
    wcel
    #
    @61
    @50
    @49
    @40
    @49
    cprime
    inss1
    #
    @0
    @51
    simpr
    #
    sseldi
    @40
    @5
    elfznn
    #
    syl
    #
    @61
    @40
    @5
    @61
    @50
    cprime
    @40
    @49
    cprime
    inss2
    #
    @65
    sseldi
    @0
    @17
    @51
    @18
    adantr
    pccld
    #
    nnexpcld
    #
    nnrpd
    #
    relogcld
    #
    syldan
    #
    @0
    @8
    cr
    wcel
    #
    @48
    @26
    adantr
    #
    @0
    @48
    wa
    #
    @43
    @8
    cle
    wbr
    #
    @43
    ce
    cfv
    #
    @8
    ce
    cfv
    #
    cle
    wbr
    #
    @76
    @42
    @4
    @78
    @79
    cle
    @0
    @12
    @40
    cprime
    wcel
    #
    @42
    @4
    cle
    wbr
    #
    @48
    @13
    @48
    @40
    @38
    wcel
    #
    @81
    @40
    @38
    cprime
    elin
    simprbi
    @40
    cN
    bposlem1
    #
    syl2an
    @76
    @42
    @0
    @48
    @51
    @42
    crp
    wcel
    @60
    @71
    syldan
    reeflogd
    @76
    @4
    @0
    @4
    crp
    wcel
    @48
    @25
    adantr
    reeflogd
    3brtr4d
    @76
    @52
    @74
    @77
    @80
    wb
    @73
    @75
    @43
    @8
    efle
    syl2anc
    mpbird
    fsumle
    @0
    @44
    @50
    @43
    vk
    csu
    @50
    @41
    @40
    clog
    cfv
    cmul
    co
    #
    vk
    csu
    #
    @6
    @0
    @39
    @50
    @43
    vk
    @59
    @0
    @48
    @51
    @43
    cc
    wcel
    @60
    @61
    @43
    @72
    recnd
    syldan
    @0
    @40
    @50
    @39
    cdif
    wcel
    #
    wa
    #
    @43
    c1
    clog
    cfv
    cc0
    @88
    @42
    c1
    clog
    @88
    @42
    @40
    cc0
    cexp
    co
    c1
    @88
    @41
    cc0
    @40
    cexp
    @88
    @41
    cn
    wcel
    #
    wn
    @41
    cc0
    wceq
    #
    @88
    @89
    @48
    @87
    @48
    wn
    @0
    @40
    @50
    @39
    eldifn
    adantl
    @0
    @87
    @89
    @48
    @0
    @87
    @89
    wa
    #
    wa
    #
    @38
    cprime
    @40
    @92
    @83
    @63
    @40
    cK
    cle
    wbr
    #
    @0
    @87
    @63
    @89
    @88
    @62
    @63
    @88
    @50
    @49
    @40
    @64
    @88
    @40
    @50
    @39
    @0
    @87
    simpr
    eldifad
    #
    sseldi
    #
    @66
    syl
    #
    adantrr
    #
    @92
    @40
    @34
    cK
    cle
    @92
    @40
    @34
    cle
    wbr
    #
    @40
    @4
    cle
    wbr
    #
    @40
    @5
    cle
    wbr
    #
    @92
    @40
    @42
    @4
    @92
    @40
    @97
    nnred
    #
    @0
    @87
    @42
    cr
    wcel
    @89
    @88
    @42
    @0
    @87
    @51
    @42
    cn
    wcel
    @94
    @70
    syldan
    nnred
    adantrr
    @0
    @21
    @91
    @22
    adantr
    #
    @92
    @40
    c1
    cexp
    co
    @40
    @42
    cle
    @92
    @40
    @92
    @40
    @97
    nncnd
    exp1d
    @92
    @40
    c1
    @41
    @101
    @92
    @40
    @97
    nnge1d
    @92
    @41
    cn
    c1
    cuz
    cfv
    #
    @0
    @87
    @89
    simprr
    nnuz
    syl6eleq
    leexp2ad
    eqbrtrrd
    @92
    @12
    @81
    @82
    @0
    @12
    @91
    @13
    adantr
    @0
    @87
    @81
    @89
    @88
    @50
    cprime
    @40
    @68
    @94
    sseldi
    adantrr
    #
    @84
    syl2anc
    letrd
    @0
    @87
    @100
    @89
    @88
    @62
    @100
    @95
    @40
    c1
    @5
    elfzle2
    syl
    adantrr
    @92
    @40
    cr
    wcel
    @21
    @57
    @98
    @99
    @100
    wa
    wb
    @101
    @102
    @0
    @57
    @91
    @58
    adantr
    @40
    @4
    @5
    lemin
    syl3anc
    mpbir2and
    chebbnd1lem1.1
    syl6breqr
    @92
    @55
    @83
    @63
    @93
    wa
    wb
    @92
    cK
    @0
    cK
    cn
    wcel
    @91
    @35
    adantr
    nnzd
    @40
    cK
    fznn
    syl
    mpbir2and
    @104
    elind
    expr
    mtod
    @88
    @89
    @90
    @88
    @41
    cn0
    wcel
    #
    @89
    @90
    wo
    @0
    @87
    @51
    @105
    @94
    @69
    syldan
    @41
    elnn0
    sylib
    ord
    mpd
    oveq2d
    @88
    @40
    @88
    @40
    @96
    nncnd
    exp0d
    eqtrd
    fveq2d
    log1
    syl6eq
    @0
    @49
    cfn
    wcel
    @50
    @49
    wss
    @50
    cfn
    wcel
    @0
    c1
    @5
    fzfid
    @64
    @49
    @50
    ssfi
    sylancl
    fsumss
    @0
    @50
    @43
    @85
    vk
    @61
    @40
    crp
    wcel
    @41
    cz
    wcel
    @43
    @85
    wceq
    @61
    @40
    @67
    nnrpd
    @61
    @41
    @69
    nn0zd
    @40
    @41
    relogexp
    syl2anc
    sumeq2dv
    @0
    @17
    @86
    @6
    wceq
    @18
    @5
    vk
    pclogsum
    syl
    3eqtrd
    @0
    @45
    @39
    chash
    cfv
    #
    @8
    cmul
    co
    #
    @31
    @0
    @46
    @8
    cc
    wcel
    @45
    @107
    wceq
    @47
    @0
    @8
    @26
    recnd
    @39
    @8
    vk
    fsumconst
    syl2anc
    @0
    @30
    @106
    @8
    cmul
    @0
    @55
    c2
    @103
    wcel
    @30
    @106
    wceq
    @56
    2eluzge1
    cK
    c1
    ppival2g
    sylancl
    oveq1d
    eqtr4d
    3brtr3d
    @0
    @30
    @7
    cle
    wbr
    #
    @31
    @9
    cle
    wbr
    @0
    @32
    @21
    cK
    @4
    cle
    wbr
    @108
    @36
    @22
    @0
    cK
    @34
    @4
    cle
    chebbnd1lem1.1
    @0
    @21
    @57
    @34
    @4
    cle
    wbr
    @22
    @58
    @4
    @5
    min1
    syl2anc
    syl5eqbr
    cK
    @4
    ppiwordi
    syl3anc
    @0
    @30
    @7
    @8
    @37
    @23
    @0
    @4
    @22
    @0
    c1
    c2
    @4
    @0
    1red
    #
    c2
    cr
    wcel
    #
    @0
    2re
    a1i
    @22
    c1
    c2
    clt
    wbr
    @0
    1lt2
    a1i
    @0
    c2
    c2
    c1
    cmul
    co
    #
    @4
    cle
    2t1e2
    @0
    c1
    cN
    cle
    wbr
    #
    @111
    @4
    cle
    wbr
    #
    @0
    cN
    @13
    nnge1d
    @0
    c1
    cr
    wcel
    cN
    cr
    wcel
    @110
    cc0
    c2
    clt
    wbr
    #
    wa
    #
    @112
    @113
    wb
    @109
    c4
    cN
    eluzelre
    @115
    @0
    @110
    @114
    2re
    2pos
    pm3.2i
    a1i
    c1
    cN
    c2
    lemul2
    syl3anc
    mpbid
    syl5eqbrr
    ltletrd
    rplogcld
    lemul1d
    mpbid
    letrd
    ltletrd
end
