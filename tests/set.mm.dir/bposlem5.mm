include "cmul.mm"
include "c1.mm"
include "cseq.mm"
include "cfv.mm"
include "c2.mm"
include "co.mm"
include "cppi.mm"
include "cexp.mm"
include "csqrt.mm"
include "c3.mm"
include "cdiv.mm"
include "caddc.mm"
include "ccxp.mm"
include "cn.mm"
include "wf.mm"
include "cv.mm"
include "cbc.mm"
include "cpc.mm"
include "cn0.mm"
include "wcel.mm"
include "cprime.mm"
include "id.mm"
include "cc0.mm"
include "cfz.mm"
include "c5.mm"
include "cuz.mm"
include "5nn.mm"
include "eluznn.mm"
include "sylancr.mm"
include "nnnn0d.mm"
include "fzctr.mm"
include "bccl2.mm"
include "3syl.mm"
include "pccl.mm"
include "syl2anr.mm"
include "ralrimiva.mm"
include "pcmptcl.mm"
include "simprd.mm"
include "3nn.mm"
include "cfl.mm"
include "cz.mm"
include "cle.mm"
include "wbr.mm"
include "2z.mm"
include "nnzd.mm"
include "zmulcl.mm"
include "zred.mm"
include "2nn.mm"
include "nnmulcl.mm"
include "nnrpd.mm"
include "rpge0d.mm"
include "resqrtcld.mm"
include "flcld.mm"
include "c9.mm"
include "sqrt9.mm"
include "cdc.mm"
include "cr.mm"
include "9re.mm"
include "a1i.mm"
include "10re.mm"
include "lep1.mm"
include "ax-mp.mm"
include "9p1e10.mm"
include "breqtri.mm"
include "5cn.mm"
include "2cn.mm"
include "5t2e10.mm"
include "mulcomli.mm"
include "eluzle.mm"
include "syl.mm"
include "wb.mm"
include "nnred.mm"
include "clt.mm"
include "wa.mm"
include "5re.mm"
include "2re.mm"
include "2pos.mm"
include "pm3.2i.mm"
include "lemul2.mm"
include "mp3an13.mm"
include "mpbid.mm"
include "syl5eqbrr.mm"
include "letrd.mm"
include "0re.mm"
include "9pos.mm"
include "ltleii.mm"
include "jca.mm"
include "sqrtle.mm"
include "3z.mm"
include "flge.mm"
include "sylancl.mm"
include "eluz1i.mm"
include "sylanbrc.mm"
include "syl5eqel.mm"
include "ffvelrnd.mm"
include "ppicl.mm"
include "nnexpcld.mm"
include "nndivre.mm"
include "readdcl.mm"
include "recxpcld.mm"
include "wi.mm"
include "wceq.mm"
include "fveq2.mm"
include "ppi1.mm"
include "syl6eq.mm"
include "oveq2d.mm"
include "breq12d.mm"
include "imbi2d.mm"
include "1z.mm"
include "seq1.mm"
include "1nn.mm"
include "cif.mm"
include "1nprm.mm"
include "eleq1.mm"
include "mtbiri.mm"
include "iffalsed.mm"
include "1ex.mm"
include "fvmpt.mm"
include "eqtri.mm"
include "1le1.mm"
include "eqbrtri.mm"
include "zcnd.mm"
include "exp0d.mm"
include "syl5breqr.mm"
include "ffvelrnda.mm"
include "adantr.mm"
include "ad2antrr.mm"
include "nnre.mm"
include "ad2antlr.mm"
include "nngt0.mm"
include "lemul1.mm"
include "syl3anc.mm"
include "nnz.mm"
include "adantl.mm"
include "ppiprm.mm"
include "sylan.mm"
include "cc.mm"
include "expp1d.mm"
include "eqtrd.mm"
include "breq2d.mm"
include "bitr4d.mm"
include "simpr.mm"
include "nnuz.mm"
include "syl6eleq.mm"
include "seqp1.mm"
include "peano2nn.mm"
include "oveq1.mm"
include "oveq12d.mm"
include "ifbieq1d.mm"
include "ovex.mm"
include "ifex.mm"
include "iftrue.mm"
include "sylan9eq.mm"
include "bposlem1.mm"
include "eqbrtrd.mm"
include "simpld.mm"
include "ffvelrn.mm"
include "syl2an.mm"
include "nnmulcld.mm"
include "letr.mm"
include "mpand.mm"
include "sylbid.mm"
include "wn.mm"
include "iffalse.mm"
include "nncnd.mm"
include "mulid1d.mm"
include "3eqtrd.mm"
include "ppinprm.mm"
include "biimprd.mm"
include "pm2.61dan.mm"
include "expcom.mm"
include "a2d.mm"
include "nnind.mm"
include "mpcom.mm"
include "cxpexp.mm"
include "syl2anc.mm"
include "nn0red.mm"
include "nn0ge0d.mm"
include "ppiub.mm"
include "flle.mm"
include "syl5eqbr.mm"
include "3re.mm"
include "3pos.mm"
include "lediv1.mm"
include "leadd1dd.mm"
include "2t1e2.mm"
include "nnge1d.mm"
include "1re.mm"
include "eluz2gt1.mm"
include "cxpled.mm"
include "eqbrtrrd.mm"

theorem bposlem5
  let wph: wff ph
  let vn: setvar n
  let cF: class F
  let cK: class K
  let cM: class M
  let cN: class N
  let vp: setvar p
  let vk: setvar k
  let vx: setvar x
  assume bpos.1: |- ( ph -> N e. ( ZZ>= ` 5 ) )
  assume bpos.2: |- ( ph -> -. E. p e. Prime ( N < p /\ p <_ ( 2 x. N ) ) )
  assume bpos.3: |- F = ( n e. NN |-> if ( n e. Prime , ( n ^ ( n pCnt ( ( 2 x. N ) _C N ) ) ) , 1 ) )
  assume bpos.4: |- K = ( |_ ` ( ( 2 x. N ) / 3 ) )
  assume bpos.5: |- M = ( |_ ` ( sqrt ` ( 2 x. N ) ) )

  disjoint F p
  disjoint n p
  disjoint K n
  disjoint K p
  disjoint M p
  disjoint N n
  disjoint N p
  disjoint n ph
  disjoint p ph
  disjoint k p
  disjoint k x
  disjoint F k
  disjoint p x
  disjoint F x
  disjoint M x
  disjoint k n
  disjoint N k
  disjoint n x
  disjoint N x
  disjoint k ph
  disjoint ph x
  assert |- ( ph -> ( seq 1 ( x. , F ) ` M ) <_ ( ( 2 x. N ) ^c ( ( ( sqrt ` ( 2 x. N ) ) / 3 ) + 2 ) ) )

  proof
    wph
    cM
    cmul
    cF
    c1
    cseq
    #
    cfv
    #
    c2
    cN
    cmul
    co
    #
    cM
    cppi
    cfv
    #
    cexp
    co
    #
    @2
    @2
    csqrt
    cfv
    #
    c3
    cdiv
    co
    #
    c2
    caddc
    co
    #
    ccxp
    co
    #
    wph
    @1
    wph
    cn
    cn
    cM
    @0
    wph
    cn
    cn
    cF
    wf
    #
    cn
    cn
    @0
    wf
    #
    wph
    vn
    cv
    #
    @2
    cN
    cbc
    co
    #
    cpc
    co
    #
    vn
    cF
    bpos.3
    wph
    @13
    cn0
    wcel
    #
    vn
    cprime
    @11
    cprime
    wcel
    #
    @15
    @12
    cn
    wcel
    #
    @14
    wph
    @15
    id
    wph
    cN
    cn0
    wcel
    cN
    cc0
    @2
    cfz
    co
    wcel
    @16
    wph
    cN
    wph
    c5
    cn
    wcel
    cN
    c5
    cuz
    cfv
    wcel
    #
    cN
    cn
    wcel
    #
    5nn
    bpos.1
    cN
    c5
    eluznn
    sylancr
    #
    nnnn0d
    cN
    fzctr
    cN
    @2
    bccl2
    3syl
    @11
    @12
    pccl
    syl2anr
    ralrimiva
    pcmptcl
    #
    simprd
    #
    wph
    c3
    cn
    wcel
    #
    cM
    c3
    cuz
    cfv
    #
    wcel
    cM
    cn
    wcel
    #
    3nn
    wph
    cM
    @5
    cfl
    cfv
    #
    @23
    bpos.5
    wph
    @25
    cz
    wcel
    c3
    @25
    cle
    wbr
    #
    @25
    @23
    wcel
    wph
    @5
    wph
    @2
    wph
    @2
    wph
    c2
    cz
    wcel
    cN
    cz
    wcel
    @2
    cz
    wcel
    #
    2z
    wph
    cN
    @19
    nnzd
    c2
    cN
    zmulcl
    sylancr
    #
    zred
    #
    wph
    @2
    wph
    @2
    wph
    c2
    cn
    wcel
    @18
    @2
    cn
    wcel
    #
    2nn
    @19
    c2
    cN
    nnmulcl
    sylancr
    #
    nnrpd
    rpge0d
    #
    resqrtcld
    #
    flcld
    wph
    c3
    @5
    cle
    wbr
    #
    @26
    wph
    c3
    c9
    csqrt
    cfv
    #
    @5
    cle
    sqrt9
    wph
    c9
    @2
    cle
    wbr
    #
    @35
    @5
    cle
    wbr
    #
    wph
    c9
    c1
    cc0
    cdc
    #
    @2
    c9
    cr
    wcel
    #
    wph
    9re
    a1i
    @38
    cr
    wcel
    wph
    10re
    a1i
    @29
    c9
    @38
    cle
    wbr
    wph
    c9
    c9
    c1
    caddc
    co
    #
    @38
    cle
    @39
    c9
    @40
    cle
    wbr
    9re
    c9
    lep1
    ax-mp
    9p1e10
    breqtri
    a1i
    wph
    @38
    c2
    c5
    cmul
    co
    #
    @2
    cle
    c5
    c2
    @38
    5cn
    2cn
    5t2e10
    mulcomli
    wph
    c5
    cN
    cle
    wbr
    #
    @41
    @2
    cle
    wbr
    #
    wph
    @17
    @42
    bpos.1
    c5
    cN
    eluzle
    syl
    wph
    cN
    cr
    wcel
    #
    @42
    @43
    wb
    #
    wph
    cN
    @19
    nnred
    #
    c5
    cr
    wcel
    @44
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
    @45
    5re
    @47
    @48
    2re
    2pos
    pm3.2i
    #
    c5
    cN
    c2
    lemul2
    mp3an13
    syl
    mpbid
    syl5eqbrr
    letrd
    wph
    @39
    cc0
    c9
    cle
    wbr
    #
    wa
    @2
    cr
    wcel
    #
    cc0
    @2
    cle
    wbr
    #
    wa
    @36
    @37
    wb
    @39
    @51
    9re
    cc0
    c9
    0re
    9re
    9pos
    ltleii
    pm3.2i
    wph
    @52
    @53
    @29
    @32
    jca
    c9
    @2
    sqrtle
    sylancr
    mpbid
    syl5eqbrr
    wph
    @5
    cr
    wcel
    #
    c3
    cz
    wcel
    @34
    @26
    wb
    @33
    3z
    @5
    c3
    flge
    sylancl
    mpbid
    c3
    @25
    3z
    eluz1i
    sylanbrc
    syl5eqel
    cM
    c3
    eluznn
    sylancr
    #
    ffvelrnd
    nnred
    wph
    @4
    wph
    @2
    @3
    @31
    wph
    cM
    cr
    wcel
    #
    @3
    cn0
    wcel
    #
    wph
    cM
    @55
    nnred
    #
    cM
    ppicl
    syl
    #
    nnexpcld
    nnred
    wph
    @2
    @7
    @29
    @32
    wph
    @6
    cr
    wcel
    #
    @47
    @7
    cr
    wcel
    wph
    @54
    @22
    @60
    @33
    3nn
    @5
    c3
    nndivre
    sylancl
    #
    2re
    @6
    c2
    readdcl
    sylancl
    #
    recxpcld
    @24
    wph
    @1
    @4
    cle
    wbr
    #
    @55
    wph
    vx
    cv
    #
    @0
    cfv
    #
    @2
    @64
    cppi
    cfv
    #
    cexp
    co
    #
    cle
    wbr
    #
    wi
    wph
    c1
    @0
    cfv
    #
    @2
    cc0
    cexp
    co
    #
    cle
    wbr
    #
    wi
    wph
    vk
    cv
    #
    @0
    cfv
    #
    @2
    @72
    cppi
    cfv
    #
    cexp
    co
    #
    cle
    wbr
    #
    wi
    wph
    @72
    c1
    caddc
    co
    #
    @0
    cfv
    #
    @2
    @77
    cppi
    cfv
    #
    cexp
    co
    #
    cle
    wbr
    #
    wi
    wph
    @63
    wi
    vx
    vk
    cM
    @64
    c1
    wceq
    #
    @68
    @71
    wph
    @82
    @65
    @69
    @67
    @70
    cle
    @64
    c1
    @0
    fveq2
    @82
    @66
    cc0
    @2
    cexp
    @82
    @66
    c1
    cppi
    cfv
    cc0
    @64
    c1
    cppi
    fveq2
    ppi1
    syl6eq
    oveq2d
    breq12d
    imbi2d
    @64
    @72
    wceq
    #
    @68
    @76
    wph
    @83
    @65
    @73
    @67
    @75
    cle
    @64
    @72
    @0
    fveq2
    @83
    @66
    @74
    @2
    cexp
    @64
    @72
    cppi
    fveq2
    oveq2d
    breq12d
    imbi2d
    @64
    @77
    wceq
    #
    @68
    @81
    wph
    @84
    @65
    @78
    @67
    @80
    cle
    @64
    @77
    @0
    fveq2
    @84
    @66
    @79
    @2
    cexp
    @64
    @77
    cppi
    fveq2
    oveq2d
    breq12d
    imbi2d
    @64
    cM
    wceq
    #
    @68
    @63
    wph
    @85
    @65
    @1
    @67
    @4
    cle
    @64
    cM
    @0
    fveq2
    @85
    @66
    @3
    @2
    cexp
    @64
    cM
    cppi
    fveq2
    oveq2d
    breq12d
    imbi2d
    wph
    @69
    c1
    @70
    cle
    @69
    c1
    c1
    cle
    @69
    c1
    cF
    cfv
    #
    c1
    c1
    cz
    wcel
    @69
    @86
    wceq
    1z
    cmul
    cF
    c1
    seq1
    ax-mp
    c1
    cn
    wcel
    @86
    c1
    wceq
    1nn
    vn
    c1
    @15
    @11
    @13
    cexp
    co
    #
    c1
    cif
    #
    c1
    cn
    cF
    @11
    c1
    wceq
    #
    @15
    @87
    c1
    @89
    @15
    c1
    cprime
    wcel
    1nprm
    @11
    c1
    cprime
    eleq1
    mtbiri
    iffalsed
    bpos.3
    1ex
    fvmpt
    ax-mp
    eqtri
    1le1
    eqbrtri
    wph
    @2
    wph
    @2
    @28
    zcnd
    #
    exp0d
    syl5breqr
    @72
    cn
    wcel
    #
    wph
    @76
    @81
    wph
    @91
    @76
    @81
    wi
    #
    wph
    @91
    wa
    #
    @77
    cprime
    wcel
    #
    @92
    @93
    @94
    wa
    #
    @76
    @73
    @2
    cmul
    co
    #
    @80
    cle
    wbr
    #
    @81
    @95
    @76
    @96
    @75
    @2
    cmul
    co
    #
    cle
    wbr
    #
    @97
    @95
    @73
    cr
    wcel
    #
    @75
    cr
    wcel
    @52
    cc0
    @2
    clt
    wbr
    #
    wa
    #
    @76
    @99
    wb
    @93
    @100
    @94
    @93
    @73
    wph
    cn
    cn
    @72
    @0
    @21
    ffvelrnda
    #
    nnred
    adantr
    @95
    @75
    @95
    @2
    @74
    wph
    @30
    @91
    @94
    @31
    ad2antrr
    @95
    @72
    cr
    wcel
    #
    @74
    cn0
    wcel
    @91
    @104
    wph
    @94
    @72
    nnre
    ad2antlr
    @72
    ppicl
    syl
    #
    nnexpcld
    nnred
    wph
    @102
    @91
    @94
    wph
    @30
    @102
    @31
    @30
    @52
    @101
    @2
    nnre
    @2
    nngt0
    jca
    syl
    ad2antrr
    @73
    @75
    @2
    lemul1
    syl3anc
    @95
    @80
    @98
    @96
    cle
    @95
    @80
    @2
    @74
    c1
    caddc
    co
    #
    cexp
    co
    @98
    @95
    @79
    @106
    @2
    cexp
    @93
    @72
    cz
    wcel
    #
    @94
    @79
    @106
    wceq
    @91
    @107
    wph
    @72
    nnz
    adantl
    #
    @72
    ppiprm
    sylan
    oveq2d
    @95
    @2
    @74
    wph
    @2
    cc
    wcel
    #
    @91
    @94
    @90
    ad2antrr
    @105
    expp1d
    eqtrd
    breq2d
    bitr4d
    @95
    @78
    @96
    cle
    wbr
    #
    @97
    @81
    @95
    @78
    @73
    @77
    cF
    cfv
    #
    cmul
    co
    #
    @96
    cle
    @93
    @78
    @112
    wceq
    #
    @94
    @93
    @72
    c1
    cuz
    cfv
    #
    wcel
    @113
    @93
    @72
    cn
    @114
    wph
    @91
    simpr
    nnuz
    syl6eleq
    cmul
    cF
    c1
    @72
    seqp1
    syl
    #
    adantr
    @95
    @111
    @2
    cle
    wbr
    #
    @112
    @96
    cle
    wbr
    #
    @95
    @111
    @77
    @77
    @12
    cpc
    co
    #
    cexp
    co
    #
    @2
    cle
    @93
    @94
    @111
    @94
    @119
    c1
    cif
    #
    @119
    @93
    @77
    cn
    wcel
    #
    @111
    @120
    wceq
    @91
    @121
    wph
    @72
    peano2nn
    #
    adantl
    #
    vn
    @77
    @88
    @120
    cn
    cF
    @11
    @77
    wceq
    #
    @15
    @94
    @87
    @119
    c1
    @11
    @77
    cprime
    eleq1
    @124
    @11
    @77
    @13
    @118
    cexp
    @124
    id
    @11
    @77
    @12
    cpc
    oveq1
    oveq12d
    ifbieq1d
    bpos.3
    @94
    @119
    c1
    @77
    @118
    cexp
    ovex
    1ex
    ifex
    fvmpt
    syl
    #
    @94
    @119
    c1
    iftrue
    sylan9eq
    @93
    @18
    @94
    @119
    @2
    cle
    wbr
    wph
    @18
    @91
    @19
    adantr
    @77
    cN
    bposlem1
    sylan
    eqbrtrd
    @95
    @111
    cr
    wcel
    #
    @52
    @100
    cc0
    @73
    clt
    wbr
    #
    wa
    #
    @116
    @117
    wb
    @93
    @126
    @94
    @93
    @111
    wph
    @9
    @121
    @111
    cn
    wcel
    @91
    wph
    @9
    @10
    @20
    simpld
    @122
    cn
    cn
    @77
    cF
    ffvelrn
    syl2an
    nnred
    adantr
    wph
    @52
    @91
    @94
    @29
    ad2antrr
    @93
    @128
    @94
    @93
    @73
    cn
    wcel
    #
    @128
    @103
    @129
    @100
    @127
    @73
    nnre
    @73
    nngt0
    jca
    syl
    adantr
    @111
    @2
    @73
    lemul2
    syl3anc
    mpbid
    eqbrtrd
    @93
    @110
    @97
    wa
    @81
    wi
    #
    @94
    @93
    @78
    cr
    wcel
    @96
    cr
    wcel
    @80
    cr
    wcel
    @130
    @93
    @78
    wph
    @10
    @121
    @78
    cn
    wcel
    @91
    @21
    @122
    cn
    cn
    @77
    @0
    ffvelrn
    syl2an
    nnred
    @93
    @96
    @93
    @73
    @2
    @103
    wph
    @30
    @91
    @31
    adantr
    #
    nnmulcld
    nnred
    @93
    @80
    @93
    @2
    @79
    @131
    @93
    @77
    cr
    wcel
    @79
    cn0
    wcel
    @93
    @77
    @123
    nnred
    @77
    ppicl
    syl
    nnexpcld
    nnred
    @78
    @96
    @80
    letr
    syl3anc
    adantr
    mpand
    sylbid
    @93
    @94
    wn
    #
    wa
    #
    @81
    @76
    @133
    @78
    @73
    @80
    @75
    cle
    @133
    @78
    @112
    @73
    c1
    cmul
    co
    @73
    @93
    @113
    @132
    @115
    adantr
    @133
    @111
    c1
    @73
    cmul
    @93
    @132
    @111
    @120
    c1
    @125
    @94
    @119
    c1
    iffalse
    sylan9eq
    oveq2d
    @133
    @73
    @133
    @73
    @93
    @129
    @132
    @103
    adantr
    nncnd
    mulid1d
    3eqtrd
    @133
    @79
    @74
    @2
    cexp
    @93
    @107
    @132
    @79
    @74
    wceq
    @108
    @72
    ppinprm
    sylan
    oveq2d
    breq12d
    biimprd
    pm2.61dan
    expcom
    a2d
    nnind
    mpcom
    wph
    @2
    @3
    ccxp
    co
    #
    @4
    @8
    cle
    wph
    @109
    @57
    @134
    @4
    wceq
    @90
    @59
    @2
    @3
    cxpexp
    syl2anc
    wph
    @3
    @7
    cle
    wbr
    @134
    @8
    cle
    wbr
    wph
    @3
    cM
    c3
    cdiv
    co
    #
    c2
    caddc
    co
    #
    @7
    wph
    @3
    @59
    nn0red
    #
    wph
    @135
    cr
    wcel
    #
    @47
    @136
    cr
    wcel
    wph
    @56
    @22
    @138
    @58
    3nn
    cM
    c3
    nndivre
    sylancl
    #
    2re
    @135
    c2
    readdcl
    sylancl
    @62
    wph
    @56
    cc0
    cM
    cle
    wbr
    @3
    @136
    cle
    wbr
    @58
    wph
    cM
    wph
    cM
    @55
    nnnn0d
    nn0ge0d
    cM
    ppiub
    syl2anc
    wph
    @135
    @6
    c2
    @139
    @61
    @47
    wph
    2re
    a1i
    wph
    cM
    @5
    cle
    wbr
    #
    @135
    @6
    cle
    wbr
    #
    wph
    cM
    @25
    @5
    cle
    bpos.5
    wph
    @54
    @25
    @5
    cle
    wbr
    @33
    @5
    flle
    syl
    syl5eqbr
    wph
    @56
    @54
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
    @140
    @141
    wb
    @58
    @33
    @144
    wph
    @142
    @143
    3re
    3pos
    pm3.2i
    a1i
    cM
    @5
    c3
    lediv1
    syl3anc
    mpbid
    leadd1dd
    letrd
    wph
    @2
    @3
    @7
    @29
    wph
    @2
    c2
    cuz
    cfv
    wcel
    #
    c1
    @2
    clt
    wbr
    wph
    @27
    c2
    @2
    cle
    wbr
    @145
    @28
    wph
    c2
    c2
    c1
    cmul
    co
    #
    @2
    cle
    2t1e2
    wph
    c1
    cN
    cle
    wbr
    #
    @146
    @2
    cle
    wbr
    #
    wph
    cN
    @19
    nnge1d
    wph
    @44
    @147
    @148
    wb
    #
    @46
    c1
    cr
    wcel
    @44
    @49
    @149
    1re
    @50
    c1
    cN
    c2
    lemul2
    mp3an13
    syl
    mpbid
    syl5eqbrr
    c2
    @2
    2z
    eluz1i
    sylanbrc
    @2
    eluz2gt1
    syl
    @137
    @62
    cxpled
    mpbid
    eqbrtrrd
    letrd
end
