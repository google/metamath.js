include "cmul.mm"
include "c1.mm"
include "cseq.mm"
include "cfv.mm"
include "c2.mm"
include "co.mm"
include "cbc.mm"
include "wceq.mm"
include "cv.mm"
include "cpc.mm"
include "cprime.mm"
include "wral.mm"
include "wcel.mm"
include "wa.mm"
include "cle.mm"
include "wbr.mm"
include "cc0.mm"
include "cif.mm"
include "cn0.mm"
include "simpr.mm"
include "cn.mm"
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
include "adantr.mm"
include "pccld.mm"
include "ralrimiva.mm"
include "cz.mm"
include "c3.mm"
include "cdiv.mm"
include "cfl.mm"
include "cr.mm"
include "2nn.mm"
include "nnmulcl.mm"
include "nnred.mm"
include "3nn.mm"
include "nndivre.mm"
include "sylancl.mm"
include "flcld.mm"
include "syl5eqel.mm"
include "3re.mm"
include "a1i.mm"
include "5re.mm"
include "3lt5.mm"
include "ltleii.mm"
include "eluzle.mm"
include "syl.mm"
include "letrd.mm"
include "wb.mm"
include "clt.mm"
include "2re.mm"
include "2pos.mm"
include "pm3.2i.mm"
include "lemul2.mm"
include "mp3an13.mm"
include "mpbid.mm"
include "3pos.mm"
include "lemuldiv.mm"
include "2z.mm"
include "flge.mm"
include "syl6breqr.mm"
include "eluz1i.mm"
include "sylanbrc.mm"
include "eluz2nn.mm"
include "oveq1.mm"
include "pcmpt.mm"
include "iftrue.mm"
include "adantl.mm"
include "wn.mm"
include "iffalse.mm"
include "zred.mm"
include "prmz.mm"
include "ltnle.mm"
include "syl2an.mm"
include "biimpar.mm"
include "ad2antrr.mm"
include "simplr.mm"
include "ad2antlr.mm"
include "simprl.mm"
include "lelttrd.mm"
include "syl5eqbrr.mm"
include "fllt.mm"
include "syl2anc.mm"
include "mpbird.mm"
include "simprr.mm"
include "bposlem2.mm"
include "expr.mm"
include "wi.mm"
include "wrex.mm"
include "rspe.mm"
include "adantll.mm"
include "pm2.21dd.mm"
include "cdvds.mm"
include "cfa.mm"
include "nnzd.mm"
include "faccl.mm"
include "nnmulcld.mm"
include "dvdsmul1.mm"
include "bcctr.mm"
include "oveq1d.mm"
include "nncnd.mm"
include "nnne0d.mm"
include "divcan1d.mm"
include "eqtrd.mm"
include "breqtrd.mm"
include "dvdstr.mm"
include "syl3anc.mm"
include "mpan2d.mm"
include "prmfac1.mm"
include "3expia.mm"
include "sylan.mm"
include "syld.mm"
include "con3d.mm"
include "id.mm"
include "pceq0.mm"
include "syl2anr.mm"
include "sylibrd.mm"
include "pm2.61d.mm"
include "ex.mm"
include "wo.mm"
include "lelttric.mm"
include "mpjaod.mm"
include "syldan.mm"
include "eqtr4d.mm"
include "pm2.61dan.mm"
include "wf.mm"
include "pcmptcl.mm"
include "simprd.mm"
include "ffvelrnd.mm"
include "pc11.mm"

theorem bposlem3
  let wph: wff ph
  let vn: setvar n
  let cF: class F
  let cK: class K
  let cN: class N
  let vp: setvar p
  let vk: setvar k
  let vx: setvar x
  let cM: class M
  assume bpos.1: |- ( ph -> N e. ( ZZ>= ` 5 ) )
  assume bpos.2: |- ( ph -> -. E. p e. Prime ( N < p /\ p <_ ( 2 x. N ) ) )
  assume bpos.3: |- F = ( n e. NN |-> if ( n e. Prime , ( n ^ ( n pCnt ( ( 2 x. N ) _C N ) ) ) , 1 ) )
  assume bpos.4: |- K = ( |_ ` ( ( 2 x. N ) / 3 ) )

  disjoint F p
  disjoint n p
  disjoint K n
  disjoint K p
  disjoint N n
  disjoint N p
  disjoint n ph
  disjoint p ph
  disjoint k p
  disjoint k x
  disjoint F k
  disjoint p x
  disjoint F x
  disjoint M p
  disjoint M x
  disjoint k n
  disjoint N k
  disjoint n x
  disjoint N x
  disjoint k ph
  disjoint ph x
  assert |- ( ph -> ( seq 1 ( x. , F ) ` K ) = ( ( 2 x. N ) _C N ) )

  proof
    wph
    cK
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
    cN
    cbc
    co
    #
    wceq
    #
    vp
    cv
    #
    @1
    cpc
    co
    #
    @5
    @3
    cpc
    co
    #
    wceq
    #
    vp
    cprime
    wral
    #
    wph
    @8
    vp
    cprime
    wph
    @5
    cprime
    wcel
    #
    wa
    #
    @6
    @5
    cK
    cle
    wbr
    #
    @7
    cc0
    cif
    #
    @7
    @11
    vn
    cv
    #
    @3
    cpc
    co
    #
    @7
    @5
    vn
    cF
    cK
    bpos.3
    wph
    @15
    cn0
    wcel
    #
    vn
    cprime
    wral
    @10
    wph
    @16
    vn
    cprime
    wph
    @14
    cprime
    wcel
    #
    wa
    @14
    @3
    wph
    @17
    simpr
    wph
    @3
    cn
    wcel
    #
    @17
    wph
    cN
    cn0
    wcel
    #
    cN
    cc0
    @2
    cfz
    co
    wcel
    @18
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
    #
    cN
    fzctr
    cN
    @2
    bccl2
    3syl
    #
    adantr
    pccld
    ralrimiva
    #
    adantr
    wph
    cK
    cn
    wcel
    #
    @10
    wph
    cK
    c2
    cuz
    cfv
    wcel
    #
    @26
    wph
    cK
    cz
    wcel
    c2
    cK
    cle
    wbr
    #
    @27
    wph
    cK
    @2
    c3
    cdiv
    co
    #
    cfl
    cfv
    #
    cz
    bpos.4
    wph
    @29
    wph
    @2
    cr
    wcel
    #
    c3
    cn
    wcel
    @29
    cr
    wcel
    #
    wph
    @2
    wph
    c2
    cn
    wcel
    @21
    @2
    cn
    wcel
    2nn
    @22
    c2
    cN
    nnmulcl
    sylancr
    #
    nnred
    #
    3nn
    @2
    c3
    nndivre
    sylancl
    #
    flcld
    syl5eqel
    #
    wph
    c2
    @30
    cK
    cle
    wph
    c2
    @29
    cle
    wbr
    #
    c2
    @30
    cle
    wbr
    #
    wph
    c2
    c3
    cmul
    co
    @2
    cle
    wbr
    #
    @37
    wph
    c3
    cN
    cle
    wbr
    #
    @39
    wph
    c3
    c5
    cN
    c3
    cr
    wcel
    #
    wph
    3re
    a1i
    c5
    cr
    wcel
    wph
    5re
    a1i
    wph
    cN
    @22
    nnred
    #
    c3
    c5
    cle
    wbr
    wph
    c3
    c5
    3re
    5re
    3lt5
    ltleii
    a1i
    wph
    @20
    c5
    cN
    cle
    wbr
    bpos.1
    c5
    cN
    eluzle
    syl
    letrd
    wph
    cN
    cr
    wcel
    #
    @40
    @39
    wb
    #
    @42
    @41
    @43
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
    @44
    3re
    @45
    @46
    2re
    2pos
    pm3.2i
    c3
    cN
    c2
    lemul2
    mp3an13
    syl
    mpbid
    wph
    @31
    @39
    @37
    wb
    #
    @34
    @45
    @31
    @41
    cc0
    c3
    clt
    wbr
    #
    wa
    @47
    2re
    @41
    @48
    3re
    3pos
    pm3.2i
    c2
    @2
    c3
    lemuldiv
    mp3an13
    syl
    mpbid
    wph
    @32
    c2
    cz
    wcel
    @37
    @38
    wb
    @35
    2z
    @29
    c2
    flge
    sylancl
    mpbid
    bpos.4
    syl6breqr
    #
    c2
    cK
    2z
    eluz1i
    sylanbrc
    cK
    eluz2nn
    syl
    #
    adantr
    wph
    @10
    simpr
    @14
    @5
    @3
    cpc
    oveq1
    pcmpt
    @11
    @12
    @13
    @7
    wceq
    #
    @12
    @51
    @11
    @12
    @7
    cc0
    iftrue
    adantl
    @11
    @12
    wn
    #
    wa
    @13
    cc0
    @7
    @52
    @13
    cc0
    wceq
    @11
    @12
    @7
    cc0
    iffalse
    adantl
    @11
    @52
    cK
    @5
    clt
    wbr
    #
    @7
    cc0
    wceq
    #
    @11
    @53
    @52
    wph
    cK
    cr
    wcel
    #
    @5
    cr
    wcel
    #
    @53
    @52
    wb
    @10
    wph
    cK
    @36
    zred
    #
    @10
    @5
    @5
    prmz
    #
    zred
    #
    cK
    @5
    ltnle
    syl2an
    biimpar
    @11
    @53
    wa
    @5
    cN
    cle
    wbr
    #
    @54
    cN
    @5
    clt
    wbr
    #
    @11
    @53
    @60
    @54
    @11
    @53
    @60
    wa
    #
    wa
    #
    @5
    cN
    wph
    @21
    @10
    @62
    @22
    ad2antrr
    wph
    @10
    @62
    simplr
    @63
    c2
    cK
    @5
    @45
    @63
    2re
    a1i
    wph
    @55
    @10
    @62
    @57
    ad2antrr
    @63
    @5
    @10
    @5
    cz
    wcel
    #
    wph
    @62
    @58
    ad2antlr
    #
    zred
    wph
    @28
    @10
    @62
    @49
    ad2antrr
    @11
    @53
    @60
    simprl
    #
    lelttrd
    @63
    @29
    @5
    clt
    wbr
    #
    @30
    @5
    clt
    wbr
    #
    @63
    @30
    cK
    @5
    clt
    bpos.4
    @66
    syl5eqbrr
    @63
    @32
    @64
    @67
    @68
    wb
    wph
    @32
    @10
    @62
    @35
    ad2antrr
    @65
    @29
    @5
    fllt
    syl2anc
    mpbird
    @11
    @53
    @60
    simprr
    bposlem2
    expr
    @11
    @61
    @54
    wi
    @53
    @11
    @61
    @54
    @11
    @61
    wa
    @5
    @2
    cle
    wbr
    #
    @54
    @11
    @61
    @69
    @54
    @11
    @61
    @69
    wa
    #
    wa
    @70
    vp
    cprime
    wrex
    #
    @54
    @10
    @70
    @71
    wph
    @70
    vp
    cprime
    rspe
    adantll
    wph
    @71
    wn
    @10
    @70
    bpos.2
    ad2antrr
    pm2.21dd
    expr
    @11
    @69
    wn
    #
    @54
    wi
    @61
    @11
    @72
    @5
    @3
    cdvds
    wbr
    #
    wn
    #
    @54
    @11
    @73
    @69
    @11
    @73
    @5
    @2
    cfa
    cfv
    #
    cdvds
    wbr
    #
    @69
    @11
    @73
    @3
    @75
    cdvds
    wbr
    #
    @76
    wph
    @77
    @10
    wph
    @3
    @3
    cN
    cfa
    cfv
    #
    @78
    cmul
    co
    #
    cmul
    co
    #
    @75
    cdvds
    wph
    @3
    cz
    wcel
    #
    @79
    cz
    wcel
    @3
    @80
    cdvds
    wbr
    wph
    @3
    @24
    nnzd
    #
    wph
    @79
    wph
    @78
    @78
    wph
    @19
    @78
    cn
    wcel
    @23
    cN
    faccl
    syl
    #
    @83
    nnmulcld
    #
    nnzd
    @3
    @79
    dvdsmul1
    syl2anc
    wph
    @80
    @75
    @79
    cdiv
    co
    #
    @79
    cmul
    co
    @75
    wph
    @3
    @85
    @79
    cmul
    wph
    @19
    @3
    @85
    wceq
    @23
    cN
    bcctr
    syl
    oveq1d
    wph
    @75
    @79
    wph
    @75
    wph
    @2
    cn0
    wcel
    #
    @75
    cn
    wcel
    wph
    @2
    @33
    nnnn0d
    #
    @2
    faccl
    syl
    #
    nncnd
    wph
    @79
    @84
    nncnd
    wph
    @79
    @84
    nnne0d
    divcan1d
    eqtrd
    breqtrd
    adantr
    @11
    @64
    @81
    @75
    cz
    wcel
    #
    @73
    @77
    wa
    @76
    wi
    @10
    @64
    wph
    @58
    adantl
    wph
    @81
    @10
    @82
    adantr
    wph
    @89
    @10
    wph
    @75
    @88
    nnzd
    adantr
    @5
    @3
    @75
    dvdstr
    syl3anc
    mpan2d
    wph
    @86
    @10
    @76
    @69
    wi
    @87
    @86
    @10
    @76
    @69
    @5
    @2
    prmfac1
    3expia
    sylan
    syld
    con3d
    @10
    @10
    @18
    @54
    @74
    wb
    wph
    @10
    id
    @24
    @5
    @3
    pceq0
    syl2anr
    sylibrd
    adantr
    pm2.61d
    ex
    adantr
    @11
    @60
    @61
    wo
    #
    @53
    @10
    @56
    @43
    @90
    wph
    @59
    @42
    @5
    cN
    lelttric
    syl2anr
    adantr
    mpjaod
    syldan
    eqtr4d
    pm2.61dan
    eqtrd
    ralrimiva
    wph
    @1
    cn0
    wcel
    @3
    cn0
    wcel
    @4
    @9
    wb
    wph
    @1
    wph
    cn
    cn
    cK
    @0
    wph
    cn
    cn
    cF
    wf
    cn
    cn
    @0
    wf
    wph
    @15
    vn
    cF
    bpos.3
    @25
    pcmptcl
    simprd
    @50
    ffvelrnd
    nnnn0d
    wph
    @3
    @24
    nnnn0d
    @1
    @3
    vp
    pc11
    syl2anc
    mpbird
end
