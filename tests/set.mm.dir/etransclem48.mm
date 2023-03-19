include "cv.mm"
include "clt.mm"
include "wbr.mm"
include "cprime.mm"
include "wrex.mm"
include "cc0.mm"
include "wne.mm"
include "cabs.mm"
include "cfv.mm"
include "c1.mm"
include "wa.mm"
include "cz.mm"
include "cn.mm"
include "wcel.mm"
include "cfa.mm"
include "ctp.mm"
include "wss.mm"
include "cn0.mm"
include "cply.mm"
include "wf.mm"
include "c0p.mm"
include "csn.mm"
include "eldifad.mm"
include "0zd.mm"
include "coef2.mm"
include "syl2anc.mm"
include "0nn0.mm"
include "a1i.mm"
include "ffvelrnd.mm"
include "zabscl.mm"
include "syl.mm"
include "cdgr.mm"
include "dgrcl.mm"
include "syl5eqel.mm"
include "faccld.mm"
include "nnzd.mm"
include "cuz.mm"
include "wral.mm"
include "crab.mm"
include "ssrab2.mm"
include "nn0ssz.mm"
include "sstri.mm"
include "cr.mm"
include "cinf.mm"
include "c0.mm"
include "nn0uz.mm"
include "sseqtri.mm"
include "crp.mm"
include "1rp.mm"
include "cli.mm"
include "cmul.mm"
include "co.mm"
include "cmpt.mm"
include "caddc.mm"
include "cexp.mm"
include "cdiv.mm"
include "cvv.mm"
include "nfv.mm"
include "nfmpt1.mm"
include "nfcxfr.mm"
include "nn0ex.mm"
include "mptex.mm"
include "cfz.mm"
include "ceu.mm"
include "ccxp.mm"
include "csu.mm"
include "cc.mm"
include "fzfid.mm"
include "adantr.mm"
include "elfznn0.mm"
include "adantl.mm"
include "zcnd.mm"
include "ere.mm"
include "recni.mm"
include "elfzelz.mm"
include "cxpcld.mm"
include "mulcld.mm"
include "abscld.mm"
include "recnd.mm"
include "nn0cnd.mm"
include "peano2nn0.mm"
include "expcld.mm"
include "fsumcl.mm"
include "eqidd.mm"
include "wceq.mm"
include "simpr.mm"
include "fvmptd.mm"
include "climconst.mm"
include "eqeltri.mm"
include "eqid.mm"
include "expfac.mm"
include "fvmpt2.mm"
include "eqeltrd.mm"
include "ovex.mm"
include "mpan2.mm"
include "nncnd.mm"
include "nnne0d.mm"
include "divcld.mm"
include "oveq12d.mm"
include "eqtr4d.mm"
include "climmulf.mm"
include "mul01d.mm"
include "breqtrd.mm"
include "clim0cf.mm"
include "mpbid.mm"
include "breq2.mm"
include "rexralbidv.mm"
include "rspcva.mm"
include "sylancr.mm"
include "rabn0.mm"
include "sylibr.mm"
include "infssuzcl.mm"
include "sseldi.mm"
include "tpssi.mm"
include "syl3anc.mm"
include "cxr.mm"
include "csup.mm"
include "wor.mm"
include "cfn.mm"
include "xrltso.mm"
include "tpfi.mm"
include "tpnzd.mm"
include "zssre.mm"
include "ressxr.mm"
include "syl6ss.mm"
include "fisupcl.mm"
include "syl13anc.mm"
include "sseldd.mm"
include "0red.mm"
include "nnred.mm"
include "zred.mm"
include "nngt0d.mm"
include "cle.mm"
include "fvex.mm"
include "tpid2.mm"
include "supxrub.mm"
include "sylancl.mm"
include "syl6breqr.mm"
include "ltletrd.mm"
include "elnnz.mm"
include "sylanbrc.mm"
include "prmunb.mm"
include "w3a.mm"
include "cmin.mm"
include "cprod.mm"
include "cioo.mm"
include "cneg.mm"
include "citg.mm"
include "cdif.mm"
include "3ad2ant1.mm"
include "simp2.mm"
include "prmz.mm"
include "3ad2ant2.mm"
include "tpid1.mm"
include "3adant3.mm"
include "simp3.mm"
include "lelttrd.mm"
include "oveq2.mm"
include "fveq2.mm"
include "prmnn.mm"
include "nnm1nn0.mm"
include "eqcomd.mm"
include "1zzd.mm"
include "zsubcld.mm"
include "tpid3g.mm"
include "wb.mm"
include "zltlem1.mm"
include "eluz2.mm"
include "syl3anbrc.mm"
include "raleqdv.mm"
include "elrab.mm"
include "sylib.mm"
include "simprd.mm"
include "nfcv.mm"
include "nffv.mm"
include "nfbr.mm"
include "fveq2d.mm"
include "breq1d.mm"
include "rspc.mm"
include "sylc.mm"
include "oveq2d.mm"
include "ovexd.mm"
include "nn0red.mm"
include "reexpcld.mm"
include "remulcld.mm"
include "fsumrecl.mm"
include "redivcld.mm"
include "1red.mm"
include "absltd.mm"
include "eqbrtrd.mm"
include "etransclem6.mm"
include "etransclem47.mm"
include "rexlimdv3a.mm"
include "mpd.mm"

theorem etransclem48
  let wph: wff ph
  let cA: class A
  let cC: class C
  let cQ: class Q
  let cS: class S
  let cT: class T
  let vi: setvar i
  let vj: setvar j
  let vk: setvar k
  let vn: setvar n
  let cI: class I
  let cM: class M
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let ve: setvar e
  let vp: setvar p
  assume etransclem48.q: |- ( ph -> Q e. ( ( Poly ` ZZ ) \ { 0p } ) )
  assume etransclem48.qe0: |- ( ph -> ( Q ` _e ) = 0 )
  assume etransclem48.a: |- A = ( coeff ` Q )
  assume etransclem48.a0: |- ( ph -> ( A ` 0 ) =/= 0 )
  assume etransclem48.m: |- M = ( deg ` Q )
  assume etransclem48.c: |- C = sum_ j e. ( 0 ... M ) ( ( abs ` ( ( A ` j ) x. ( _e ^c j ) ) ) x. ( M x. ( M ^ ( M + 1 ) ) ) )
  assume etransclem48.s: |- S = ( n e. NN0 |-> ( C x. ( ( ( M ^ ( M + 1 ) ) ^ n ) / ( ! ` n ) ) ) )
  assume etransclem48.i: |- I = inf ( { i e. NN0 | A. n e. ( ZZ>= ` i ) ( abs ` ( S ` n ) ) < 1 } , RR , < )
  assume etransclem48.t: |- T = sup ( { ( abs ` ( A ` 0 ) ) , ( ! ` M ) , I } , RR* , < )

  disjoint A j
  disjoint A k
  disjoint j k
  disjoint A n
  disjoint j n
  disjoint C i
  disjoint C n
  disjoint i n
  disjoint I i
  disjoint I n
  disjoint M j
  disjoint M k
  disjoint M n
  disjoint Q j
  disjoint S i
  disjoint T j
  disjoint T k
  disjoint i ph
  disjoint n ph
  disjoint j ph
  disjoint k ph
  disjoint M x
  disjoint M y
  disjoint M z
  disjoint j x
  disjoint j y
  disjoint j z
  disjoint k x
  disjoint k y
  disjoint k z
  disjoint x y
  disjoint x z
  disjoint y z
  disjoint S e
  disjoint e i
  disjoint T p
  disjoint T x
  disjoint j p
  disjoint k p
  disjoint p x
  disjoint e n
  disjoint e ph
  disjoint p ph
  disjoint ph x
  disjoint n p
  disjoint p y
  disjoint p z
  disjoint k x
  assert |- ( ph -> E. k e. ZZ ( k =/= 0 /\ ( abs ` k ) < 1 ) )

  proof
    wph
    cT
    vp
    cv
    #
    clt
    wbr
    #
    vp
    cprime
    wrex
    #
    vk
    cv
    #
    cc0
    wne
    @3
    cabs
    cfv
    c1
    clt
    wbr
    wa
    vk
    cz
    wrex
    #
    wph
    cT
    cn
    wcel
    #
    @2
    wph
    cT
    cz
    wcel
    cc0
    cT
    clt
    wbr
    @5
    wph
    cc0
    cA
    cfv
    #
    cabs
    cfv
    #
    cM
    cfa
    cfv
    #
    cI
    ctp
    #
    cz
    cT
    wph
    @7
    cz
    wcel
    #
    @8
    cz
    wcel
    cI
    cz
    wcel
    #
    @9
    cz
    wss
    wph
    @6
    cz
    wcel
    @10
    wph
    cn0
    cz
    cc0
    cA
    wph
    cQ
    cz
    cply
    cfv
    #
    wcel
    #
    cc0
    cz
    wcel
    cn0
    cz
    cA
    wf
    #
    wph
    cQ
    @12
    c0p
    csn
    #
    etransclem48.q
    eldifad
    #
    wph
    0zd
    #
    cA
    cz
    cQ
    etransclem48.a
    coef2
    syl2anc
    #
    cc0
    cn0
    wcel
    wph
    0nn0
    a1i
    ffvelrnd
    #
    @6
    zabscl
    syl
    #
    wph
    @8
    wph
    cM
    wph
    cM
    cQ
    cdgr
    cfv
    #
    cn0
    etransclem48.m
    wph
    @13
    @21
    cn0
    wcel
    @16
    cz
    cQ
    dgrcl
    syl
    syl5eqel
    #
    faccld
    #
    nnzd
    wph
    vn
    cv
    #
    cS
    cfv
    #
    cabs
    cfv
    #
    c1
    clt
    wbr
    #
    vn
    vi
    cv
    #
    cuz
    cfv
    #
    wral
    #
    vi
    cn0
    crab
    #
    cz
    cI
    @31
    cn0
    cz
    @30
    vi
    cn0
    ssrab2
    #
    nn0ssz
    sstri
    wph
    cI
    @31
    cr
    clt
    cinf
    #
    @31
    etransclem48.i
    wph
    @31
    cc0
    cuz
    cfv
    #
    wss
    @31
    c0
    wne
    #
    @33
    @31
    wcel
    @31
    cn0
    @34
    @32
    nn0uz
    sseqtri
    wph
    @30
    vi
    cn0
    wrex
    #
    @35
    wph
    c1
    crp
    wcel
    @26
    ve
    cv
    #
    clt
    wbr
    #
    vn
    @29
    wral
    vi
    cn0
    wrex
    #
    ve
    crp
    wral
    #
    @36
    1rp
    wph
    cS
    cc0
    cli
    wbr
    @40
    wph
    cS
    cC
    cc0
    cmul
    co
    cc0
    cli
    wph
    cC
    cc0
    vn
    vn
    cn0
    cC
    cmpt
    #
    vn
    cn0
    cM
    cM
    c1
    caddc
    co
    #
    cexp
    co
    #
    @24
    cexp
    co
    #
    @24
    cfa
    cfv
    #
    cdiv
    co
    #
    cmpt
    #
    cS
    cc0
    cvv
    cn0
    wph
    vn
    nfv
    vn
    cn0
    cC
    nfmpt1
    vn
    cn0
    @46
    nfmpt1
    vn
    cS
    vn
    cn0
    cC
    @46
    cmul
    co
    #
    cmpt
    #
    etransclem48.s
    vn
    cn0
    @48
    nfmpt1
    nfcxfr
    #
    nn0uz
    @17
    wph
    cC
    vi
    @41
    cc0
    cvv
    cn0
    nn0uz
    @17
    @41
    cvv
    wcel
    wph
    vn
    cn0
    cC
    nn0ex
    mptex
    a1i
    wph
    cC
    cc0
    cM
    cfz
    co
    #
    vj
    cv
    #
    cA
    cfv
    #
    ceu
    @52
    ccxp
    co
    #
    cmul
    co
    #
    cabs
    cfv
    #
    cM
    @43
    cmul
    co
    #
    cmul
    co
    #
    vj
    csu
    #
    cc
    etransclem48.c
    wph
    @51
    @58
    vj
    wph
    cc0
    cM
    fzfid
    #
    wph
    @52
    @51
    wcel
    #
    wa
    #
    @56
    @57
    @62
    @56
    @62
    @55
    @62
    @53
    @54
    @62
    @53
    @62
    cn0
    cz
    @52
    cA
    wph
    @14
    @61
    @18
    adantr
    @61
    @52
    cn0
    wcel
    wph
    @52
    cM
    elfznn0
    adantl
    ffvelrnd
    zcnd
    @62
    ceu
    @52
    ceu
    cc
    wcel
    @62
    ceu
    ere
    recni
    a1i
    @61
    @52
    cc
    wcel
    wph
    @61
    @52
    @52
    cc0
    cM
    elfzelz
    zcnd
    adantl
    cxpcld
    mulcld
    abscld
    #
    recnd
    wph
    @57
    cc
    wcel
    @61
    wph
    cM
    @43
    wph
    cM
    @22
    nn0cnd
    #
    wph
    cM
    @42
    @64
    wph
    cM
    cn0
    wcel
    @42
    cn0
    wcel
    @22
    cM
    peano2nn0
    syl
    #
    expcld
    #
    mulcld
    adantr
    mulcld
    fsumcl
    #
    syl5eqel
    #
    wph
    @28
    cn0
    wcel
    #
    wa
    #
    vn
    @28
    cC
    cC
    cn0
    @41
    cc
    @70
    @41
    eqidd
    @70
    @24
    @28
    wceq
    wa
    cC
    eqidd
    wph
    @69
    simpr
    wph
    cC
    cc
    wcel
    #
    @69
    @68
    adantr
    fvmptd
    climconst
    cS
    cvv
    wcel
    wph
    cS
    @49
    cvv
    etransclem48.s
    vn
    cn0
    @48
    nn0ex
    mptex
    eqeltri
    a1i
    #
    wph
    @43
    cc
    wcel
    #
    @47
    cc0
    cli
    wbr
    @66
    @43
    vn
    @47
    @47
    eqid
    #
    expfac
    syl
    wph
    @24
    cn0
    wcel
    #
    wa
    #
    @24
    @41
    cfv
    #
    cC
    cc
    @76
    @75
    @71
    @77
    cC
    wceq
    wph
    @75
    simpr
    #
    wph
    @71
    @75
    @68
    adantr
    #
    vn
    cn0
    cC
    cc
    @41
    @41
    eqid
    fvmpt2
    syl2anc
    #
    @79
    eqeltrd
    #
    @76
    @24
    @47
    cfv
    #
    @46
    cc
    @75
    @82
    @46
    wceq
    #
    wph
    @75
    @46
    cvv
    wcel
    @83
    @44
    @45
    cdiv
    ovex
    vn
    cn0
    @46
    cvv
    @47
    @74
    fvmpt2
    mpan2
    adantl
    #
    @76
    @44
    @45
    @76
    @43
    @24
    wph
    @73
    @75
    @66
    adantr
    @78
    expcld
    @76
    @45
    @76
    @24
    @78
    faccld
    #
    nncnd
    @76
    @45
    @85
    nnne0d
    divcld
    eqeltrd
    #
    @76
    @25
    @48
    @77
    @82
    cmul
    co
    #
    @75
    @25
    @48
    wceq
    #
    wph
    @75
    @48
    cvv
    wcel
    @88
    cC
    @46
    cmul
    ovex
    vn
    cn0
    @48
    cvv
    cS
    etransclem48.s
    fvmpt2
    mpan2
    adantl
    @76
    @77
    cC
    @82
    @46
    cmul
    @80
    @84
    oveq12d
    eqtr4d
    #
    climmulf
    wph
    cC
    @68
    mul01d
    breqtrd
    wph
    ve
    @25
    vi
    vn
    cS
    cc0
    cvv
    cn0
    @50
    nn0uz
    @17
    @72
    @76
    @25
    eqidd
    @76
    @25
    @87
    cc
    @89
    @76
    @77
    @82
    @81
    @86
    mulcld
    eqeltrd
    clim0cf
    mpbid
    @39
    @36
    ve
    c1
    crp
    @37
    c1
    wceq
    @38
    @27
    vi
    vn
    cn0
    @29
    @37
    c1
    @26
    clt
    breq2
    rexralbidv
    rspcva
    sylancr
    @30
    vi
    cn0
    rabn0
    sylibr
    @31
    cc0
    infssuzcl
    sylancr
    syl5eqel
    #
    sseldi
    #
    @7
    @8
    cI
    cz
    tpssi
    syl3anc
    #
    wph
    cT
    @9
    cxr
    clt
    csup
    #
    @9
    etransclem48.t
    wph
    cxr
    clt
    wor
    #
    @9
    cfn
    wcel
    #
    @9
    c0
    wne
    @9
    cxr
    wss
    #
    @93
    @9
    wcel
    @94
    wph
    xrltso
    a1i
    @95
    wph
    @7
    @8
    cI
    tpfi
    a1i
    wph
    @7
    @8
    cI
    cz
    @20
    tpnzd
    wph
    @9
    cz
    cxr
    @92
    cz
    cr
    cxr
    zssre
    ressxr
    sstri
    syl6ss
    #
    cxr
    @9
    clt
    fisupcl
    syl13anc
    syl5eqel
    sseldd
    #
    wph
    cc0
    @8
    cT
    wph
    0red
    wph
    @8
    @23
    nnred
    #
    wph
    cT
    @98
    zred
    #
    wph
    @8
    @23
    nngt0d
    wph
    @8
    @93
    cT
    cle
    wph
    @96
    @8
    @9
    wcel
    @8
    @93
    cle
    wbr
    @97
    @7
    @8
    cI
    cM
    cfa
    fvex
    tpid2
    @9
    @8
    supxrub
    sylancl
    etransclem48.t
    syl6breqr
    #
    ltletrd
    cT
    elnnz
    sylanbrc
    cT
    vp
    prmunb
    syl
    wph
    @1
    @4
    vp
    cprime
    wph
    @0
    cprime
    wcel
    #
    @1
    w3a
    #
    vx
    cA
    @0
    cQ
    vj
    vk
    vy
    cr
    vy
    cv
    #
    @0
    c1
    cmin
    co
    #
    cexp
    co
    c1
    cM
    cfz
    co
    @104
    vz
    cv
    cmin
    co
    @0
    cexp
    co
    vz
    cprod
    cmul
    co
    cmpt
    #
    @51
    @55
    vx
    cc0
    @52
    cioo
    co
    ceu
    vx
    cv
    #
    cneg
    ccxp
    co
    @107
    @106
    cfv
    cmul
    co
    citg
    cmul
    co
    vj
    csu
    #
    @105
    cfa
    cfv
    #
    cdiv
    co
    #
    @108
    cM
    wph
    @102
    cQ
    @12
    @15
    cdif
    wcel
    @1
    etransclem48.q
    3ad2ant1
    wph
    @102
    ceu
    cQ
    cfv
    cc0
    wceq
    @1
    etransclem48.qe0
    3ad2ant1
    etransclem48.a
    wph
    @102
    @6
    cc0
    wne
    @1
    etransclem48.a0
    3ad2ant1
    etransclem48.m
    wph
    @102
    @1
    simp2
    @103
    @7
    cT
    @0
    @103
    @6
    wph
    @102
    @6
    cc
    wcel
    @1
    wph
    @6
    @19
    zcnd
    3ad2ant1
    abscld
    wph
    @102
    cT
    cr
    wcel
    @1
    @100
    3ad2ant1
    #
    @102
    wph
    @0
    cr
    wcel
    @1
    @102
    @0
    @0
    prmz
    #
    zred
    3ad2ant2
    #
    wph
    @102
    @7
    cT
    cle
    wbr
    @1
    wph
    @102
    wa
    #
    @7
    @93
    cT
    cle
    @114
    @96
    @7
    @9
    wcel
    @7
    @93
    cle
    wbr
    wph
    @96
    @102
    @97
    adantr
    @7
    @8
    cI
    @6
    cabs
    fvex
    tpid1
    @9
    @7
    supxrub
    sylancl
    etransclem48.t
    syl6breqr
    3adant3
    wph
    @102
    @1
    simp3
    #
    lelttrd
    @103
    @8
    cT
    @0
    wph
    @102
    @8
    cr
    wcel
    @1
    @99
    3ad2ant1
    @111
    @113
    wph
    @102
    @8
    cT
    cle
    wbr
    @1
    @101
    3ad2ant1
    @115
    lelttrd
    @103
    @59
    @43
    @105
    cexp
    co
    #
    @109
    cdiv
    co
    #
    cmul
    co
    #
    @105
    cS
    cfv
    #
    c1
    clt
    wph
    @102
    @118
    @119
    wceq
    @1
    @114
    @119
    @118
    @114
    vn
    @105
    @48
    @118
    cn0
    cS
    cc
    cS
    @49
    wceq
    @114
    etransclem48.s
    a1i
    #
    @24
    @105
    wceq
    #
    @48
    @118
    wceq
    @114
    @121
    cC
    @59
    @46
    @117
    cmul
    cC
    @59
    wceq
    @121
    etransclem48.c
    a1i
    @121
    @44
    @116
    @45
    @109
    cdiv
    @24
    @105
    @43
    cexp
    oveq2
    @24
    @105
    cfa
    fveq2
    oveq12d
    #
    oveq12d
    adantl
    @102
    @105
    cn0
    wcel
    #
    wph
    @102
    @0
    cn
    wcel
    @123
    @0
    prmnn
    @0
    nnm1nn0
    syl
    #
    adantl
    #
    @114
    @59
    @117
    wph
    @59
    cc
    wcel
    @102
    @67
    adantr
    @114
    @116
    @109
    @114
    @43
    @105
    wph
    @73
    @102
    @66
    adantr
    @125
    expcld
    @102
    @109
    cc
    wcel
    wph
    @102
    @109
    @102
    @105
    @124
    faccld
    #
    nncnd
    adantl
    @102
    @109
    cc0
    wne
    wph
    @102
    @109
    @126
    nnne0d
    adantl
    #
    divcld
    mulcld
    fvmptd
    eqcomd
    3adant3
    @103
    c1
    cneg
    @119
    clt
    wbr
    #
    @119
    c1
    clt
    wbr
    #
    @103
    @119
    cabs
    cfv
    #
    c1
    clt
    wbr
    #
    @128
    @129
    wa
    @103
    @105
    cI
    cuz
    cfv
    #
    wcel
    #
    @27
    vn
    @132
    wral
    #
    @131
    @103
    @11
    @105
    cz
    wcel
    #
    cI
    @105
    cle
    wbr
    #
    @133
    wph
    @102
    @11
    @1
    @91
    3ad2ant1
    #
    @102
    wph
    @135
    @1
    @102
    @0
    c1
    @112
    @102
    1zzd
    zsubcld
    3ad2ant2
    @103
    cI
    @0
    clt
    wbr
    #
    @136
    @103
    cI
    cT
    @0
    @103
    cI
    @137
    zred
    @111
    @113
    wph
    @102
    cI
    cT
    cle
    wbr
    @1
    wph
    cI
    @93
    cT
    cle
    wph
    @96
    cI
    @9
    wcel
    #
    cI
    @93
    cle
    wbr
    @97
    wph
    @11
    @139
    @91
    cI
    cz
    @7
    @8
    tpid3g
    syl
    @9
    cI
    supxrub
    syl2anc
    etransclem48.t
    syl6breqr
    3ad2ant1
    @115
    lelttrd
    @103
    @11
    @0
    cz
    wcel
    #
    @138
    @136
    wb
    @137
    @102
    wph
    @140
    @1
    @112
    3ad2ant2
    cI
    @0
    zltlem1
    syl2anc
    mpbid
    cI
    @105
    eluz2
    syl3anbrc
    @103
    cI
    cn0
    wcel
    #
    @134
    @103
    cI
    @31
    wcel
    #
    @141
    @134
    wa
    wph
    @102
    @142
    @1
    @90
    3ad2ant1
    @30
    @134
    vi
    cI
    cn0
    @28
    cI
    wceq
    @27
    vn
    @29
    @132
    @28
    cI
    cuz
    fveq2
    raleqdv
    elrab
    sylib
    simprd
    @27
    @131
    vn
    @105
    @132
    vn
    @130
    c1
    clt
    vn
    @119
    cabs
    vn
    cabs
    nfcv
    vn
    @105
    cS
    @50
    vn
    @105
    nfcv
    nffv
    nffv
    vn
    clt
    nfcv
    vn
    c1
    nfcv
    nfbr
    @121
    @26
    @130
    c1
    clt
    @121
    @25
    @119
    cabs
    @24
    @105
    cS
    fveq2
    fveq2d
    breq1d
    rspc
    sylc
    @103
    @119
    c1
    wph
    @102
    @119
    cr
    wcel
    @1
    @114
    @119
    cC
    @117
    cmul
    co
    #
    cr
    @114
    vn
    @105
    @48
    @143
    cn0
    cS
    cvv
    @120
    @121
    @48
    @143
    wceq
    @114
    @121
    @46
    @117
    cC
    cmul
    @122
    oveq2d
    adantl
    @125
    @114
    cC
    @117
    cmul
    ovexd
    fvmptd
    @114
    cC
    @117
    wph
    cC
    cr
    wcel
    @102
    wph
    cC
    @59
    cr
    etransclem48.c
    wph
    @51
    @58
    vj
    @60
    @62
    @56
    @57
    @63
    wph
    @57
    cr
    wcel
    @61
    wph
    cM
    @43
    wph
    cM
    @22
    nn0red
    #
    wph
    cM
    @42
    @144
    @65
    reexpcld
    #
    remulcld
    adantr
    remulcld
    fsumrecl
    syl5eqel
    adantr
    @114
    @116
    @109
    @114
    @43
    @105
    wph
    @43
    cr
    wcel
    @102
    @145
    adantr
    @125
    reexpcld
    @102
    @109
    cr
    wcel
    wph
    @102
    @109
    @126
    nnred
    adantl
    @127
    redivcld
    remulcld
    eqeltrd
    3adant3
    @103
    1red
    absltd
    mpbid
    simprd
    eqbrtrd
    vy
    vx
    @0
    vz
    vj
    cM
    etransclem6
    @108
    eqid
    @110
    eqid
    etransclem47
    rexlimdv3a
    mpd
end
