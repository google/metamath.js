include "cn.mm"
include "wcel.mm"
include "cmul.mm"
include "c1.mm"
include "cseq.mm"
include "cfv.mm"
include "cpc.mm"
include "co.mm"
include "cle.mm"
include "wbr.mm"
include "cc0.mm"
include "cif.mm"
include "wceq.mm"
include "cv.mm"
include "wi.mm"
include "caddc.mm"
include "fveq2.mm"
include "oveq2d.mm"
include "breq2.mm"
include "ifbid.mm"
include "eqeq12d.mm"
include "imbi2d.mm"
include "cprime.mm"
include "cz.mm"
include "1z.mm"
include "seq1.mm"
include "ax-mp.mm"
include "1nn.mm"
include "cexp.mm"
include "1nprm.mm"
include "eleq1.mm"
include "mtbiri.mm"
include "iffalsed.mm"
include "1ex.mm"
include "fvmpt.mm"
include "eqtri.mm"
include "oveq2i.mm"
include "pc1.mm"
include "syl5eq.mm"
include "clt.mm"
include "wn.mm"
include "prmgt1.mm"
include "cr.mm"
include "wb.mm"
include "1re.mm"
include "c2.mm"
include "cuz.mm"
include "prmuz2.mm"
include "eluzelre.mm"
include "syl.mm"
include "ltnle.mm"
include "sylancr.mm"
include "mpbid.mm"
include "eqtr4d.mm"
include "wa.mm"
include "adantr.mm"
include "wf.mm"
include "pcmptcl.mm"
include "simpld.mm"
include "peano2nn.mm"
include "ffvelrn.mm"
include "syl2an.mm"
include "adantrr.mm"
include "pccld.mm"
include "nn0cnd.mm"
include "addid2d.mm"
include "csb.mm"
include "cvv.mm"
include "ad2antrl.mm"
include "ovex.mm"
include "ifex.mm"
include "csbex.mm"
include "fvmpts.mm"
include "nfv.mm"
include "nfcv.mm"
include "nfcsb1v.mm"
include "nfov.mm"
include "nfif.mm"
include "id.mm"
include "csbeq1a.mm"
include "oveq12d.mm"
include "ifbieq1d.mm"
include "csbief.mm"
include "syl6eq.mm"
include "sylancl.mm"
include "simprr.mm"
include "eqeltrd.mm"
include "iftrued.mm"
include "csbeq1d.mm"
include "nfcvd.mm"
include "csbiegf.mm"
include "eqtrd.mm"
include "3eqtrd.mm"
include "cn0.mm"
include "wral.mm"
include "eleq1d.mm"
include "rspcv.mm"
include "sylc.mm"
include "pcidlem.mm"
include "syl2anc.mm"
include "oveq1.mm"
include "eqeq1d.mm"
include "syl5ibrcom.mm"
include "nnre.mm"
include "ltp1.mm"
include "peano2re.mm"
include "mpdan.mm"
include "breq1d.mm"
include "mtbid.mm"
include "eqeq2d.mm"
include "simpr.mm"
include "nnuz.mm"
include "syl6eleq.mm"
include "seqp1.mm"
include "wne.mm"
include "simprd.mm"
include "ffvelrnda.mm"
include "nnz.mm"
include "nnne0.mm"
include "jca.mm"
include "pcmul.mm"
include "syl3anc.mm"
include "prmnn.mm"
include "nnred.mm"
include "leidd.mm"
include "breqtrrd.mm"
include "3imtr4d.mm"
include "expr.mm"
include "cdvds.mm"
include "simplrr.mm"
include "necomd.mm"
include "ad2antrr.mm"
include "nfel1.mm"
include "rspc.mm"
include "prmdvdsexpr.mm"
include "necon3ad.mm"
include "mpd.mm"
include "iftrue.mm"
include "sylan9eq.mm"
include "breq2d.mm"
include "mtbird.mm"
include "pceq0.mm"
include "mpbird.mm"
include "iffalse.mm"
include "pm2.61dan.mm"
include "addid1d.mm"
include "ltlend.mm"
include "simprl.mm"
include "nnleltp1.mm"
include "biantrud.mm"
include "3bitr4rd.mm"
include "biimprd.mm"
include "pm2.61dne.mm"
include "expcom.mm"
include "a2d.mm"
include "nnind.mm"
include "mpcom.mm"

theorem pcmpt
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cP: class P
  let vn: setvar n
  let cF: class F
  let cN: class N
  let vk: setvar k
  let vm: setvar m
  let vp: setvar p
  let cM: class M
  assume pcmpt.1: |- F = ( n e. NN |-> if ( n e. Prime , ( n ^ A ) , 1 ) )
  assume pcmpt.2: |- ( ph -> A. n e. Prime A e. NN0 )
  assume pcmpt.3: |- ( ph -> N e. NN )
  assume pcmpt.4: |- ( ph -> P e. Prime )
  assume pcmpt.5: |- ( n = P -> A = B )

  disjoint B n
  disjoint P n
  disjoint k m
  disjoint k p
  disjoint A k
  disjoint m p
  disjoint A m
  disjoint A p
  disjoint k n
  disjoint B k
  disjoint n p
  disjoint B p
  disjoint F k
  disjoint F p
  disjoint M p
  disjoint N p
  disjoint P k
  disjoint m n
  disjoint P m
  disjoint P p
  disjoint k ph
  disjoint p ph
  assert |- ( ph -> ( P pCnt ( seq 1 ( x. , F ) ` N ) ) = if ( P <_ N , B , 0 ) )

  proof
    cN
    cn
    wcel
    wph
    cP
    cN
    cmul
    cF
    c1
    cseq
    #
    cfv
    #
    cpc
    co
    #
    cP
    cN
    cle
    wbr
    #
    cB
    cc0
    cif
    #
    wceq
    #
    pcmpt.3
    wph
    cP
    vp
    cv
    #
    @0
    cfv
    #
    cpc
    co
    #
    cP
    @6
    cle
    wbr
    #
    cB
    cc0
    cif
    #
    wceq
    #
    wi
    wph
    cP
    c1
    @0
    cfv
    #
    cpc
    co
    #
    cP
    c1
    cle
    wbr
    #
    cB
    cc0
    cif
    #
    wceq
    #
    wi
    wph
    cP
    vk
    cv
    #
    @0
    cfv
    #
    cpc
    co
    #
    cP
    @17
    cle
    wbr
    #
    cB
    cc0
    cif
    #
    wceq
    #
    wi
    wph
    cP
    @17
    c1
    caddc
    co
    #
    @0
    cfv
    #
    cpc
    co
    #
    cP
    @23
    cle
    wbr
    #
    cB
    cc0
    cif
    #
    wceq
    #
    wi
    wph
    @5
    wi
    vp
    vk
    cN
    @6
    c1
    wceq
    #
    @11
    @16
    wph
    @29
    @8
    @13
    @10
    @15
    @29
    @7
    @12
    cP
    cpc
    @6
    c1
    @0
    fveq2
    oveq2d
    @29
    @9
    @14
    cB
    cc0
    @6
    c1
    cP
    cle
    breq2
    ifbid
    eqeq12d
    imbi2d
    @6
    @17
    wceq
    #
    @11
    @22
    wph
    @30
    @8
    @19
    @10
    @21
    @30
    @7
    @18
    cP
    cpc
    @6
    @17
    @0
    fveq2
    oveq2d
    @30
    @9
    @20
    cB
    cc0
    @6
    @17
    cP
    cle
    breq2
    ifbid
    eqeq12d
    imbi2d
    @6
    @23
    wceq
    #
    @11
    @28
    wph
    @31
    @8
    @25
    @10
    @27
    @31
    @7
    @24
    cP
    cpc
    @6
    @23
    @0
    fveq2
    oveq2d
    @31
    @9
    @26
    cB
    cc0
    @6
    @23
    cP
    cle
    breq2
    ifbid
    eqeq12d
    imbi2d
    @6
    cN
    wceq
    #
    @11
    @5
    wph
    @32
    @8
    @2
    @10
    @4
    @32
    @7
    @1
    cP
    cpc
    @6
    cN
    @0
    fveq2
    oveq2d
    @32
    @9
    @3
    cB
    cc0
    @6
    cN
    cP
    cle
    breq2
    ifbid
    eqeq12d
    imbi2d
    wph
    cP
    cprime
    wcel
    #
    @16
    pcmpt.4
    @33
    @13
    cc0
    @15
    @33
    @13
    cP
    c1
    cpc
    co
    #
    cc0
    @12
    c1
    cP
    cpc
    @12
    c1
    cF
    cfv
    #
    c1
    c1
    cz
    wcel
    @12
    @35
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
    @35
    c1
    wceq
    1nn
    vn
    c1
    vn
    cv
    #
    cprime
    wcel
    #
    @36
    cA
    cexp
    co
    #
    c1
    cif
    #
    c1
    cn
    cF
    @36
    c1
    wceq
    #
    @37
    @38
    c1
    @40
    @37
    c1
    cprime
    wcel
    1nprm
    @36
    c1
    cprime
    eleq1
    mtbiri
    iffalsed
    pcmpt.1
    1ex
    fvmpt
    ax-mp
    eqtri
    oveq2i
    cP
    pc1
    #
    syl5eq
    @33
    @14
    cB
    cc0
    @33
    c1
    cP
    clt
    wbr
    #
    @14
    wn
    #
    cP
    prmgt1
    @33
    c1
    cr
    wcel
    cP
    cr
    wcel
    #
    @42
    @43
    wb
    1re
    @33
    cP
    c2
    cuz
    cfv
    wcel
    @44
    cP
    prmuz2
    c2
    cP
    eluzelre
    syl
    c1
    cP
    ltnle
    sylancr
    mpbid
    iffalsed
    eqtr4d
    syl
    @17
    cn
    wcel
    #
    wph
    @22
    @28
    wph
    @45
    @22
    @28
    wi
    #
    wph
    @45
    wa
    #
    @46
    @23
    cP
    wph
    @45
    @23
    cP
    wceq
    #
    @46
    wph
    @45
    @48
    wa
    #
    wa
    #
    @19
    cc0
    wceq
    #
    @19
    cP
    @23
    cF
    cfv
    #
    cpc
    co
    #
    caddc
    co
    #
    cB
    wceq
    #
    @22
    @28
    @50
    @55
    @51
    cc0
    @53
    caddc
    co
    #
    cB
    wceq
    @50
    @56
    @53
    cP
    cP
    cB
    cexp
    co
    #
    cpc
    co
    #
    cB
    @50
    @53
    @50
    @53
    @50
    cP
    @52
    wph
    @33
    @49
    pcmpt.4
    adantr
    #
    wph
    @45
    @52
    cn
    wcel
    #
    @48
    wph
    cn
    cn
    cF
    wf
    #
    @23
    cn
    wcel
    #
    @60
    @45
    wph
    @61
    cn
    cn
    @0
    wf
    #
    wph
    cA
    vn
    cF
    pcmpt.1
    pcmpt.2
    pcmptcl
    #
    simpld
    #
    @17
    peano2nn
    #
    cn
    cn
    @23
    cF
    ffvelrn
    #
    syl2an
    #
    adantrr
    pccld
    nn0cnd
    addid2d
    @50
    @52
    @57
    cP
    cpc
    @50
    @52
    @23
    cprime
    wcel
    #
    @23
    vn
    @23
    cA
    csb
    #
    cexp
    co
    #
    c1
    cif
    #
    @71
    @57
    @50
    @62
    vn
    @23
    @39
    csb
    #
    cvv
    wcel
    #
    @52
    @72
    wceq
    #
    @45
    @62
    wph
    @48
    @66
    ad2antrl
    vn
    @23
    @39
    @37
    @38
    c1
    @36
    cA
    cexp
    ovex
    1ex
    ifex
    csbex
    #
    @62
    @74
    wa
    @52
    @73
    @72
    vn
    @23
    @39
    cn
    cF
    cvv
    pcmpt.1
    fvmpts
    vn
    @23
    @39
    @72
    @17
    c1
    caddc
    ovex
    @69
    vn
    @71
    c1
    @69
    vn
    nfv
    vn
    @23
    @70
    cexp
    vn
    @23
    nfcv
    vn
    cexp
    nfcv
    vn
    @23
    cA
    nfcsb1v
    #
    nfov
    vn
    c1
    nfcv
    nfif
    @36
    @23
    wceq
    #
    @37
    @69
    @38
    @71
    c1
    @36
    @23
    cprime
    eleq1
    @78
    @36
    @23
    cA
    @70
    cexp
    @78
    id
    vn
    @23
    cA
    csbeq1a
    #
    oveq12d
    ifbieq1d
    csbief
    syl6eq
    #
    sylancl
    @50
    @69
    @71
    c1
    @50
    @23
    cP
    cprime
    wph
    @45
    @48
    simprr
    #
    @59
    eqeltrd
    iftrued
    @50
    @23
    cP
    @70
    cB
    cexp
    @81
    @50
    @70
    vn
    cP
    cA
    csb
    #
    cB
    @50
    vn
    @23
    cP
    cA
    @81
    csbeq1d
    @50
    @33
    @82
    cB
    wceq
    @59
    vn
    cP
    cA
    cB
    cprime
    @33
    vn
    cB
    nfcvd
    pcmpt.5
    csbiegf
    syl
    eqtrd
    oveq12d
    3eqtrd
    oveq2d
    @50
    @33
    cB
    cn0
    wcel
    #
    @58
    cB
    wceq
    @59
    wph
    @83
    @49
    wph
    @33
    cA
    cn0
    wcel
    #
    vn
    cprime
    wral
    #
    @83
    pcmpt.4
    pcmpt.2
    @84
    @83
    vn
    cP
    cprime
    @36
    cP
    wceq
    cA
    cB
    cn0
    pcmpt.5
    eleq1d
    rspcv
    sylc
    adantr
    cB
    cP
    pcidlem
    syl2anc
    3eqtrd
    @51
    @54
    @56
    cB
    @19
    cc0
    @53
    caddc
    oveq1
    eqeq1d
    syl5ibrcom
    @50
    @21
    cc0
    @19
    @50
    @20
    cB
    cc0
    @50
    @23
    @17
    cle
    wbr
    #
    @20
    @50
    @17
    cr
    wcel
    #
    @86
    wn
    #
    @45
    @87
    wph
    @48
    @17
    nnre
    ad2antrl
    @87
    @17
    @23
    clt
    wbr
    #
    @88
    @17
    ltp1
    @87
    @23
    cr
    wcel
    @89
    @88
    wb
    @17
    peano2re
    @17
    @23
    ltnle
    mpdan
    mpbid
    syl
    @50
    @23
    cP
    @17
    cle
    @81
    breq1d
    mtbid
    iffalsed
    eqeq2d
    @50
    @25
    @54
    @27
    cB
    wph
    @45
    @25
    @54
    wceq
    #
    @48
    @47
    @25
    cP
    @18
    @52
    cmul
    co
    #
    cpc
    co
    #
    @54
    @47
    @24
    @91
    cP
    cpc
    @47
    @17
    c1
    cuz
    cfv
    #
    wcel
    @24
    @91
    wceq
    @47
    @17
    cn
    @93
    wph
    @45
    simpr
    nnuz
    syl6eleq
    cmul
    cF
    c1
    @17
    seqp1
    syl
    oveq2d
    @47
    @33
    @18
    cz
    wcel
    #
    @18
    cc0
    wne
    #
    wa
    #
    @52
    cz
    wcel
    #
    @52
    cc0
    wne
    #
    wa
    #
    @92
    @54
    wceq
    wph
    @33
    @45
    pcmpt.4
    adantr
    @47
    @18
    cn
    wcel
    #
    @96
    wph
    cn
    cn
    @17
    @0
    wph
    @61
    @63
    @64
    simprd
    ffvelrnda
    #
    @100
    @94
    @95
    @18
    nnz
    @18
    nnne0
    jca
    syl
    @47
    @60
    @99
    @68
    @60
    @97
    @98
    @52
    nnz
    @52
    nnne0
    jca
    syl
    @18
    @52
    cP
    pcmul
    syl3anc
    eqtrd
    #
    adantrr
    @50
    @26
    cB
    cc0
    @50
    cP
    cP
    @23
    cle
    @50
    cP
    wph
    @44
    @49
    wph
    cP
    wph
    @33
    cP
    cn
    wcel
    #
    pcmpt.4
    cP
    prmnn
    syl
    #
    nnred
    adantr
    leidd
    @81
    breqtrrd
    iftrued
    eqeq12d
    3imtr4d
    expr
    wph
    @45
    @23
    cP
    wne
    #
    @46
    wph
    @45
    @105
    wa
    #
    wa
    #
    @28
    @22
    @107
    @25
    @19
    @27
    @21
    @107
    @25
    @54
    @19
    cc0
    caddc
    co
    @19
    wph
    @45
    @90
    @105
    @102
    adantrr
    @107
    @53
    cc0
    @19
    caddc
    @107
    @69
    @53
    cc0
    wceq
    #
    @107
    @69
    wa
    #
    @108
    cP
    @52
    cdvds
    wbr
    #
    wn
    #
    @109
    @110
    cP
    @71
    cdvds
    wbr
    #
    @109
    cP
    @23
    wne
    @112
    wn
    @109
    @23
    cP
    wph
    @45
    @105
    @69
    simplrr
    necomd
    @109
    @112
    cP
    @23
    @109
    @33
    @69
    @70
    cn0
    wcel
    #
    @112
    cP
    @23
    wceq
    wi
    wph
    @33
    @106
    @69
    pcmpt.4
    ad2antrr
    #
    @107
    @69
    simpr
    #
    @109
    @69
    @85
    @113
    @115
    wph
    @85
    @106
    @69
    pcmpt.2
    ad2antrr
    @84
    @113
    vn
    @23
    cprime
    vn
    @70
    cn0
    @77
    nfel1
    @78
    cA
    @70
    cn0
    @79
    eleq1d
    rspc
    sylc
    cP
    @23
    @70
    prmdvdsexpr
    syl3anc
    necon3ad
    mpd
    @109
    @52
    @71
    cP
    cdvds
    @107
    @69
    @52
    @72
    @71
    @107
    @62
    @74
    @75
    @45
    @62
    wph
    @105
    @66
    ad2antrl
    #
    @76
    @80
    sylancl
    #
    @69
    @71
    c1
    iftrue
    sylan9eq
    breq2d
    mtbird
    @109
    @33
    @60
    @108
    @111
    wb
    @114
    @107
    @60
    @69
    @107
    @61
    @62
    @60
    wph
    @61
    @106
    @65
    adantr
    @116
    @67
    syl2anc
    adantr
    cP
    @52
    pceq0
    syl2anc
    mpbird
    @107
    @69
    wn
    #
    wa
    #
    @53
    @34
    cc0
    @119
    @52
    c1
    cP
    cpc
    @107
    @118
    @52
    @72
    c1
    @117
    @69
    @71
    c1
    iffalse
    sylan9eq
    oveq2d
    wph
    @34
    cc0
    wceq
    #
    @106
    @118
    wph
    @33
    @120
    pcmpt.4
    @41
    syl
    ad2antrr
    eqtrd
    pm2.61dan
    oveq2d
    @107
    @19
    @107
    @19
    @107
    cP
    @18
    wph
    @33
    @106
    pcmpt.4
    adantr
    wph
    @45
    @100
    @105
    @101
    adantrr
    pccld
    nn0cnd
    addid1d
    3eqtrd
    @107
    @26
    @20
    cB
    cc0
    @107
    cP
    @23
    clt
    wbr
    #
    @26
    @105
    wa
    @20
    @26
    @107
    cP
    @23
    @107
    cP
    wph
    @103
    @106
    @104
    adantr
    #
    nnred
    @107
    @23
    @116
    nnred
    ltlend
    @107
    @103
    @45
    @20
    @121
    wb
    @122
    wph
    @45
    @105
    simprl
    cP
    @17
    nnleltp1
    syl2anc
    @107
    @105
    @26
    wph
    @45
    @105
    simprr
    biantrud
    3bitr4rd
    ifbid
    eqeq12d
    biimprd
    expr
    pm2.61dne
    expcom
    a2d
    nnind
    mpcom
end
