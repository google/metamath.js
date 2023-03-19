include "cn.mm"
include "wcel.mm"
include "cv.mm"
include "cdvds.mm"
include "wbr.mm"
include "cprime.mm"
include "crab.mm"
include "cpw.mm"
include "wel.mm"
include "c1.mm"
include "cc0.mm"
include "cif.mm"
include "cmpt.mm"
include "ccnv.mm"
include "cfv.mm"
include "wa.mm"
include "wss.mm"
include "cmu.mm"
include "wne.mm"
include "weq.mm"
include "fveq2.mm"
include "neeq1d.mm"
include "breq1.mm"
include "anbi12d.mm"
include "elrab2.mm"
include "simprbi.mm"
include "simprd.mm"
include "ad2antlr.mm"
include "cz.mm"
include "wi.mm"
include "prmz.mm"
include "adantl.mm"
include "simplr.mm"
include "sylib.mm"
include "simpld.mm"
include "nnzd.mm"
include "nnz.mm"
include "ad2antrr.mm"
include "dvdstr.mm"
include "syl3anc.mm"
include "mpan2d.mm"
include "ss2rabdv.mm"
include "nnex.mm"
include "prmnn.mm"
include "ssriv.mm"
include "ssexi.mm"
include "rabex.mm"
include "elpw.mm"
include "sylibr.mm"
include "cima.mm"
include "cfn.mm"
include "cn0.mm"
include "cmap.mm"
include "co.mm"
include "wf.mm"
include "wral.mm"
include "1nn0.mm"
include "0nn0.mm"
include "keepel.mm"
include "rgenw.mm"
include "eqid.mm"
include "fmpt.mm"
include "mpbi.mm"
include "a1i.mm"
include "nn0ex.mm"
include "elmap.mm"
include "cfz.mm"
include "fzfi.mm"
include "wfn.mm"
include "wb.mm"
include "ffn.mm"
include "elpreima.mm"
include "mp2b.mm"
include "elequ1.mm"
include "ifbid.mm"
include "elexi.mm"
include "fvmpt.mm"
include "eleq1d.mm"
include "biimpa.mm"
include "sylbi.mm"
include "wn.mm"
include "0nnn.mm"
include "iffalse.mm"
include "mtbiri.mm"
include "con4i.mm"
include "syl.mm"
include "elpwi.mm"
include "rabss2.mm"
include "ax-mp.mm"
include "dvdsssfz1.mm"
include "adantr.mm"
include "syl5ss.mm"
include "sstrd.mm"
include "ssfi.mm"
include "sylancr.mm"
include "wceq.mm"
include "cnveq.mm"
include "imaeq1d.mm"
include "elrab.mm"
include "sylanbrc.mm"
include "wf1o.mm"
include "1arith.mm"
include "f1ocnv.mm"
include "f1of.mm"
include "ffvelrni.mm"
include "cpc.mm"
include "cle.mm"
include "f1ocnvfv2.mm"
include "1arithlem1.mm"
include "eqtr3d.mm"
include "fveq1d.mm"
include "sylan9req.mm"
include "oveq1.mm"
include "ovex.mm"
include "1le1.mm"
include "0le1.mm"
include "keephyp.mm"
include "syl6eqbrr.mm"
include "ralrimiva.mm"
include "issqf.mm"
include "mpbird.mm"
include "iftrue.mm"
include "sselda.mm"
include "simpll.mm"
include "pcelnn.mm"
include "syl2anc.mm"
include "nnge1d.mm"
include "eqbrtrd.mm"
include "ex.mm"
include "simpr.mm"
include "pcge0.mm"
include "breq1d.mm"
include "syl5ibrcom.mm"
include "pm2.61d.mm"
include "eqbrtrrd.mm"
include "pc2dvds.mm"
include "jca.mm"
include "eqcom.mm"
include "cvv.mm"
include "simplbi.mm"
include "ad2antrl.mm"
include "mptex.mm"
include "fvmpt2.mm"
include "sylancl.mm"
include "eqeq1d.mm"
include "adantrl.mm"
include "f1ocnvfvb.mm"
include "csn.mm"
include "cpr.mm"
include "cc.mm"
include "0cnd.mm"
include "1cnd.mm"
include "0ne1.mm"
include "pw2f1olem.mm"
include "ssrab2.mm"
include "sspwb.mm"
include "simprr.mm"
include "sseldi.mm"
include "biantrurd.mm"
include "wo.mm"
include "id.mm"
include "pccl.mm"
include "syl2anr.mm"
include "elnn0.mm"
include "orcomd.mm"
include "mpbid.mm"
include "r19.21bi.mm"
include "nnle1eq1.mm"
include "syl5ibcom.mm"
include "orim2d.mm"
include "mpd.mm"
include "elpr.mm"
include "fmptd.mm"
include "adantrr.mm"
include "prex.mm"
include "3bitr4d.mm"
include "mptiniseg.mm"
include "1nn.mm"
include "syl6eqel.mm"
include "impbid2.mm"
include "bitrd.mm"
include "rabbidva.mm"
include "syl5eq.mm"
include "eqeq2d.mm"
include "3bitr3d.mm"
include "syl5bb.mm"
include "f1o2d.mm"

theorem sqff1o
  let vx: setvar x
  let cS: class S
  let vn: setvar n
  let cF: class F
  let cG: class G
  let cN: class N
  let vp: setvar p
  let vk: setvar k
  let vq: setvar q
  let vy: setvar y
  let vz: setvar z
  assume sqff1o.1: |- S = { x e. NN | ( ( mmu ` x ) =/= 0 /\ x || N ) }
  assume sqff1o.2: |- F = ( n e. S |-> { p e. Prime | p || n } )
  assume sqff1o.3: |- G = ( n e. NN |-> ( p e. Prime |-> ( p pCnt n ) ) )

  disjoint n p
  disjoint n x
  disjoint G n
  disjoint p x
  disjoint G p
  disjoint G x
  disjoint N n
  disjoint N p
  disjoint N x
  disjoint S n
  disjoint S p
  disjoint k n
  disjoint k p
  disjoint k q
  disjoint k x
  disjoint k y
  disjoint k z
  disjoint G k
  disjoint n q
  disjoint n y
  disjoint n z
  disjoint p q
  disjoint p y
  disjoint p z
  disjoint q x
  disjoint q y
  disjoint q z
  disjoint G q
  disjoint x y
  disjoint x z
  disjoint y z
  disjoint G y
  disjoint G z
  disjoint N q
  disjoint N z
  disjoint S z
  assert |- ( N e. NN -> F : S -1-1-onto-> ~P { p e. Prime | p || N } )

  proof
    cN
    cn
    wcel
    #
    vn
    vz
    cS
    vp
    cv
    #
    cN
    cdvds
    wbr
    #
    vp
    cprime
    crab
    #
    cpw
    #
    @1
    vn
    cv
    #
    cdvds
    wbr
    #
    vp
    cprime
    crab
    #
    vk
    cprime
    vk
    vz
    wel
    #
    c1
    cc0
    cif
    #
    cmpt
    #
    cG
    ccnv
    #
    cfv
    #
    cF
    sqff1o.2
    @0
    @5
    cS
    wcel
    #
    wa
    #
    @7
    @3
    wss
    @7
    @4
    wcel
    @14
    @6
    @2
    vp
    cprime
    @14
    @1
    cprime
    wcel
    #
    wa
    #
    @6
    @5
    cN
    cdvds
    wbr
    #
    @2
    @13
    @17
    @0
    @15
    @13
    @5
    cmu
    cfv
    #
    cc0
    wne
    #
    @17
    @13
    @5
    cn
    wcel
    #
    @19
    @17
    wa
    #
    vx
    cv
    #
    cmu
    cfv
    #
    cc0
    wne
    #
    @22
    cN
    cdvds
    wbr
    #
    wa
    #
    @21
    vx
    @5
    cn
    cS
    vx
    vn
    weq
    #
    @24
    @19
    @25
    @17
    @27
    @23
    @18
    cc0
    @22
    @5
    cmu
    fveq2
    neeq1d
    @22
    @5
    cN
    cdvds
    breq1
    anbi12d
    sqff1o.1
    elrab2
    #
    simprbi
    #
    simprd
    ad2antlr
    @16
    @1
    cz
    wcel
    #
    @5
    cz
    wcel
    cN
    cz
    wcel
    #
    @6
    @17
    wa
    @2
    wi
    @15
    @30
    @14
    @1
    prmz
    adantl
    @16
    @5
    @16
    @20
    @21
    @16
    @13
    @20
    @21
    wa
    @0
    @13
    @15
    simplr
    @28
    sylib
    simpld
    #
    nnzd
    @0
    @31
    @13
    @15
    cN
    nnz
    #
    ad2antrr
    @1
    @5
    cN
    dvdstr
    syl3anc
    mpan2d
    ss2rabdv
    @7
    @3
    @6
    vp
    cprime
    cprime
    cn
    nnex
    vp
    cprime
    cn
    @1
    prmnn
    ssriv
    #
    ssexi
    #
    rabex
    elpw
    sylibr
    @0
    vz
    cv
    #
    @4
    wcel
    #
    wa
    #
    @12
    cn
    wcel
    #
    @12
    cmu
    cfv
    #
    cc0
    wne
    #
    @12
    cN
    cdvds
    wbr
    #
    wa
    #
    @12
    cS
    wcel
    @38
    @10
    vy
    cv
    #
    ccnv
    #
    cn
    cima
    #
    cfn
    wcel
    #
    vy
    cn0
    cprime
    cmap
    co
    #
    crab
    #
    wcel
    #
    @39
    @38
    @10
    @48
    wcel
    #
    @10
    ccnv
    #
    cn
    cima
    #
    cfn
    wcel
    #
    @50
    @38
    cprime
    cn0
    @10
    wf
    #
    @51
    @55
    @38
    @9
    cn0
    wcel
    #
    vk
    cprime
    wral
    @55
    @56
    vk
    cprime
    @8
    c1
    cc0
    cn0
    1nn0
    0nn0
    keepel
    rgenw
    vk
    cprime
    cn0
    @9
    @10
    @10
    eqid
    #
    fmpt
    mpbi
    #
    a1i
    cn0
    cprime
    @10
    nn0ex
    @35
    elmap
    sylibr
    @38
    c1
    cN
    cfz
    co
    #
    cfn
    wcel
    @53
    @59
    wss
    @54
    c1
    cN
    fzfi
    @38
    @53
    @36
    @59
    vx
    @53
    @36
    @22
    @53
    wcel
    #
    vx
    vz
    wel
    #
    c1
    cc0
    cif
    #
    cn
    wcel
    #
    @61
    @60
    @22
    cprime
    wcel
    #
    @22
    @10
    cfv
    #
    cn
    wcel
    #
    wa
    #
    @63
    @55
    @10
    cprime
    wfn
    @60
    @67
    wb
    @58
    cprime
    cn0
    @10
    ffn
    cprime
    @22
    cn
    @10
    elpreima
    mp2b
    @64
    @66
    @63
    @64
    @65
    @62
    cn
    vk
    @22
    @9
    @62
    cprime
    @10
    vk
    vx
    weq
    @8
    @61
    c1
    cc0
    vk
    vx
    vz
    elequ1
    ifbid
    @57
    @62
    cn0
    @61
    c1
    cc0
    cn0
    1nn0
    0nn0
    keepel
    elexi
    fvmpt
    eleq1d
    biimpa
    sylbi
    @61
    @63
    @61
    wn
    #
    @63
    cc0
    cn
    wcel
    0nnn
    @68
    @62
    cc0
    cn
    @61
    c1
    cc0
    iffalse
    eleq1d
    mtbiri
    con4i
    syl
    ssriv
    @38
    @36
    @3
    @59
    @37
    @36
    @3
    wss
    @0
    @36
    @3
    elpwi
    adantl
    #
    @38
    @3
    @2
    vp
    cn
    crab
    #
    @59
    cprime
    cn
    wss
    @3
    @70
    wss
    @34
    @2
    vp
    cprime
    cn
    rabss2
    ax-mp
    @0
    @70
    @59
    wss
    @37
    cN
    vp
    dvdsssfz1
    adantr
    syl5ss
    sstrd
    syl5ss
    @59
    @53
    ssfi
    sylancr
    @47
    @54
    vy
    @10
    @48
    @44
    @10
    wceq
    #
    @46
    @53
    cfn
    @71
    @45
    @52
    cn
    @44
    @10
    cnveq
    imaeq1d
    eleq1d
    elrab
    sylanbrc
    #
    @49
    cn
    @10
    @11
    cn
    @49
    cG
    wf1o
    #
    @49
    cn
    @11
    wf1o
    @49
    cn
    @11
    wf
    @49
    vy
    vn
    cG
    vp
    sqff1o.3
    @49
    eqid
    1arith
    #
    cn
    @49
    cG
    f1ocnv
    @49
    cn
    @11
    f1of
    mp2b
    ffvelrni
    syl
    #
    @38
    @41
    @42
    @38
    @41
    vq
    cv
    #
    @12
    cpc
    co
    #
    c1
    cle
    wbr
    #
    vq
    cprime
    wral
    #
    @38
    @78
    vq
    cprime
    @38
    @76
    cprime
    wcel
    #
    wa
    #
    @77
    vq
    vz
    wel
    #
    c1
    cc0
    cif
    #
    c1
    cle
    @81
    @76
    vp
    cprime
    @1
    @12
    cpc
    co
    #
    cmpt
    #
    cfv
    #
    @83
    @77
    @38
    @80
    @86
    @76
    @10
    cfv
    @83
    @38
    @76
    @10
    @85
    @38
    @12
    cG
    cfv
    #
    @10
    @85
    @38
    @73
    @50
    @87
    @10
    wceq
    @74
    @72
    cn
    @49
    @10
    cG
    f1ocnvfv2
    sylancr
    @38
    @39
    @87
    @85
    wceq
    @75
    vn
    cG
    @12
    vp
    sqff1o.3
    1arithlem1
    syl
    eqtr3d
    fveq1d
    vk
    @76
    @9
    @83
    cprime
    @10
    vk
    vq
    weq
    @8
    @82
    c1
    cc0
    vk
    vq
    vz
    elequ1
    ifbid
    @57
    @83
    cn0
    @82
    c1
    cc0
    cn0
    1nn0
    0nn0
    keepel
    elexi
    fvmpt
    sylan9req
    @80
    @86
    @77
    wceq
    @38
    vp
    @76
    @84
    @77
    cprime
    @85
    @1
    @76
    @12
    cpc
    oveq1
    @85
    eqid
    @76
    @12
    cpc
    ovex
    fvmpt
    adantl
    eqtr3d
    #
    @82
    c1
    c1
    cle
    wbr
    cc0
    c1
    cle
    wbr
    @83
    c1
    cle
    wbr
    c1
    cc0
    c1
    @83
    c1
    cle
    breq1
    cc0
    @83
    c1
    cle
    breq1
    1le1
    0le1
    keephyp
    syl6eqbrr
    ralrimiva
    @38
    @39
    @41
    @79
    wb
    @75
    @12
    vq
    issqf
    syl
    mpbird
    @38
    @42
    @77
    @76
    cN
    cpc
    co
    #
    cle
    wbr
    #
    vq
    cprime
    wral
    #
    @38
    @90
    vq
    cprime
    @81
    @83
    @77
    @89
    cle
    @88
    @81
    @82
    @83
    @89
    cle
    wbr
    #
    @38
    @82
    @92
    wi
    @80
    @38
    @82
    @92
    @38
    @82
    wa
    #
    @83
    c1
    @89
    cle
    @82
    @83
    c1
    wceq
    @38
    @82
    c1
    cc0
    iftrue
    adantl
    @93
    @89
    @93
    @89
    cn
    wcel
    #
    @76
    cN
    cdvds
    wbr
    #
    @93
    @80
    @95
    @93
    @76
    @3
    wcel
    @80
    @95
    wa
    @38
    @36
    @3
    @76
    @69
    sselda
    @2
    @95
    vp
    @76
    cprime
    @1
    @76
    cN
    cdvds
    breq1
    elrab
    sylib
    #
    simprd
    @93
    @80
    @0
    @94
    @95
    wb
    @93
    @80
    @95
    @96
    simpld
    @0
    @37
    @82
    simpll
    @76
    cN
    pcelnn
    syl2anc
    mpbird
    nnge1d
    eqbrtrd
    ex
    adantr
    @81
    @92
    @82
    wn
    #
    cc0
    @89
    cle
    wbr
    #
    @81
    @80
    @31
    @98
    @38
    @80
    simpr
    @0
    @31
    @37
    @80
    @33
    ad2antrr
    @76
    cN
    pcge0
    syl2anc
    @97
    @83
    cc0
    @89
    cle
    @82
    c1
    cc0
    iffalse
    breq1d
    syl5ibrcom
    pm2.61d
    eqbrtrrd
    ralrimiva
    @38
    @12
    cz
    wcel
    @31
    @42
    @91
    wb
    @38
    @12
    @75
    nnzd
    @0
    @31
    @37
    @33
    adantr
    @12
    cN
    vq
    pc2dvds
    syl2anc
    mpbird
    jca
    @26
    @43
    vx
    @12
    cn
    cS
    @22
    @12
    wceq
    #
    @24
    @41
    @25
    @42
    @99
    @23
    @40
    cc0
    @22
    @12
    cmu
    fveq2
    neeq1d
    @22
    @12
    cN
    cdvds
    breq1
    anbi12d
    sqff1o.1
    elrab2
    sylanbrc
    @5
    @12
    wceq
    @12
    @5
    wceq
    #
    @0
    @13
    @37
    wa
    wa
    #
    @36
    @7
    wceq
    #
    @5
    @12
    eqcom
    @101
    @5
    cG
    cfv
    #
    @10
    wceq
    #
    vp
    cprime
    @1
    @5
    cpc
    co
    #
    cmpt
    #
    @10
    wceq
    #
    @100
    @102
    @101
    @103
    @106
    @10
    @101
    @20
    @106
    cvv
    wcel
    @103
    @106
    wceq
    @13
    @20
    @0
    @37
    @13
    @20
    @21
    @28
    simplbi
    #
    ad2antrl
    #
    vp
    cprime
    @105
    @35
    mptex
    vn
    cn
    @106
    cvv
    cG
    sqff1o.3
    fvmpt2
    sylancl
    eqeq1d
    @101
    @73
    @20
    @50
    @104
    @100
    wb
    @73
    @101
    @74
    a1i
    @109
    @0
    @37
    @50
    @13
    @72
    adantrl
    cn
    @49
    @5
    @10
    cG
    f1ocnvfvb
    syl3anc
    @101
    @107
    @36
    @106
    ccnv
    c1
    csn
    cima
    #
    wceq
    #
    @102
    @101
    @36
    cprime
    cpw
    #
    wcel
    #
    @107
    wa
    @106
    cc0
    c1
    cpr
    #
    cprime
    cmap
    co
    wcel
    #
    @111
    wa
    @107
    @111
    @101
    vk
    cprime
    cc0
    c1
    @36
    @106
    cvv
    cc
    cprime
    cvv
    wcel
    @101
    @35
    a1i
    @101
    0cnd
    @101
    1cnd
    cc0
    c1
    wne
    @101
    0ne1
    a1i
    pw2f1olem
    @101
    @113
    @107
    @101
    @4
    @112
    @36
    @3
    cprime
    wss
    @4
    @112
    wss
    @2
    vp
    cprime
    ssrab2
    @3
    cprime
    sspwb
    mpbi
    @0
    @13
    @37
    simprr
    sseldi
    biantrurd
    @101
    @115
    @111
    @101
    cprime
    @114
    @106
    wf
    #
    @115
    @0
    @13
    @116
    @37
    @14
    vp
    cprime
    @105
    @114
    @106
    @16
    @105
    cc0
    wceq
    #
    @105
    c1
    wceq
    #
    wo
    #
    @105
    @114
    wcel
    @16
    @117
    @105
    cn
    wcel
    #
    wo
    @119
    @16
    @120
    @117
    @16
    @105
    cn0
    wcel
    #
    @120
    @117
    wo
    @15
    @15
    @20
    @121
    @14
    @15
    id
    @13
    @20
    @0
    @108
    adantl
    #
    @1
    @5
    pccl
    syl2anr
    @105
    elnn0
    sylib
    orcomd
    @16
    @120
    @118
    @117
    @16
    @105
    c1
    cle
    wbr
    #
    @120
    @118
    @14
    @123
    vp
    cprime
    @14
    @19
    @123
    vp
    cprime
    wral
    #
    @13
    @19
    @0
    @13
    @19
    @17
    @29
    simpld
    adantl
    @14
    @20
    @19
    @124
    wb
    @122
    @5
    vp
    issqf
    syl
    mpbid
    r19.21bi
    @105
    nnle1eq1
    syl5ibcom
    #
    orim2d
    mpd
    @105
    cc0
    c1
    @1
    @5
    cpc
    ovex
    elpr
    sylibr
    @106
    eqid
    #
    fmptd
    adantrr
    @114
    cprime
    @106
    cc0
    c1
    prex
    @35
    elmap
    sylibr
    biantrurd
    3bitr4d
    @101
    @110
    @7
    @36
    @101
    @110
    @118
    vp
    cprime
    crab
    #
    @7
    c1
    cn0
    wcel
    @110
    @127
    wceq
    1nn0
    vp
    cprime
    @105
    c1
    @106
    cn0
    @126
    mptiniseg
    ax-mp
    @0
    @13
    @127
    @7
    wceq
    @37
    @14
    @118
    @6
    vp
    cprime
    @16
    @118
    @120
    @6
    @16
    @118
    @120
    @118
    @105
    c1
    cn
    @118
    id
    1nn
    syl6eqel
    @125
    impbid2
    @16
    @15
    @20
    @120
    @6
    wb
    @14
    @15
    simpr
    @32
    @1
    @5
    pcelnn
    syl2anc
    bitrd
    rabbidva
    adantrr
    syl5eq
    eqeq2d
    bitrd
    3bitr3d
    syl5bb
    f1o2d
end
