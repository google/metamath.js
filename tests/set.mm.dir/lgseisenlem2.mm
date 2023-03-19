include "c1.mm"
include "cmin.mm"
include "co.mm"
include "c2.mm"
include "cdiv.mm"
include "cfz.mm"
include "wf1.mm"
include "wf1o.mm"
include "wf.mm"
include "cv.mm"
include "cfv.mm"
include "wceq.mm"
include "weq.mm"
include "wi.mm"
include "wral.mm"
include "lgseisenlem1.mm"
include "wcel.mm"
include "wa.mm"
include "cneg.mm"
include "cexp.mm"
include "cmul.mm"
include "cmo.mm"
include "oveq2.mm"
include "oveq2d.mm"
include "oveq1d.mm"
include "3eqtr4g.mm"
include "oveq12d.mm"
include "ovex.mm"
include "fvmpt.mm"
include "ad2antrl.mm"
include "cvv.mm"
include "fvmpt2.mm"
include "mpan2.mm"
include "ad2antll.mm"
include "eqeq12d.mm"
include "cc.mm"
include "cc0.mm"
include "wne.mm"
include "wb.mm"
include "cz.mm"
include "cn0.mm"
include "cprime.mm"
include "csn.mm"
include "cdif.mm"
include "adantr.mm"
include "eldifad.mm"
include "prmz.mm"
include "syl.mm"
include "2z.mm"
include "elfzelz.mm"
include "zmulcl.mm"
include "sylancr.mm"
include "zmulcld.mm"
include "cn.mm"
include "prmnn.mm"
include "zmodcld.mm"
include "syl5eqel.mm"
include "nn0zd.mm"
include "m1expcl.mm"
include "nn0cnd.mm"
include "2cnd.mm"
include "2ne0.mm"
include "a1i.mm"
include "div11.mm"
include "syl112anc.mm"
include "nnrpd.mm"
include "eqidd.mm"
include "oveq1i.mm"
include "cr.mm"
include "crp.mm"
include "zred.mm"
include "modabs2.mm"
include "syl2anc.mm"
include "syl5eq.mm"
include "modmul12d.mm"
include "cdvds.mm"
include "wbr.mm"
include "moddvds.mm"
include "syl3anc.mm"
include "zcnd.mm"
include "subdid.mm"
include "mul12d.mm"
include "eqtrd.mm"
include "breq2d.mm"
include "cgcd.mm"
include "prmrp.mm"
include "mpbird.mm"
include "zsubcld.mm"
include "coprmdvds.mm"
include "mpan2d.mm"
include "dvdsmultr2.mm"
include "caddc.mm"
include "neg1cn.mm"
include "expaddd.mm"
include "mulassd.mm"
include "eqtr2d.mm"
include "ax-1cn.mm"
include "ax-1ne0.mm"
include "divneg2.mm"
include "mp3an.mm"
include "1div1e1.mm"
include "negeqi.mm"
include "eqtr3i.mm"
include "neg1ne0.mm"
include "exprecd.mm"
include "syl5eqr.mm"
include "expne0d.mm"
include "recidd.mm"
include "mulid2d.mm"
include "3eqtr3d.mm"
include "eqcom.mm"
include "mulm1d.mm"
include "eqeq2d.mm"
include "syl5bb.mm"
include "znegcld.mm"
include "wn.mm"
include "cle.mm"
include "elfznn.mm"
include "nnaddcld.mm"
include "nnred.mm"
include "oddprm.mm"
include "elfzle2.mm"
include "le2addd.mm"
include "peano2rem.mm"
include "recnd.mm"
include "2halvesd.mm"
include "breqtrd.mm"
include "peano2zm.mm"
include "fznn.mm"
include "3syl.mm"
include "mpbir2and.mm"
include "fzm1ndvds.mm"
include "eldifsni.mm"
include "2prm.mm"
include "sylancl.mm"
include "nnzd.mm"
include "mtod.mm"
include "subnegd.mm"
include "adddid.mm"
include "eqtr4d.mm"
include "mtbird.mm"
include "pm2.21d.mm"
include "sylbid.mm"
include "oveq1.mm"
include "eqeq1d.mm"
include "imbi1d.mm"
include "syl5ibrcom.mm"
include "clt.mm"
include "2nn.mm"
include "nnmulcl.mm"
include "nnnn0d.mm"
include "nn0ge0d.mm"
include "2re.mm"
include "2pos.mm"
include "lemuldiv2.mm"
include "zltlem1.mm"
include "modid.mm"
include "syl22anc.mm"
include "biimpd.mm"
include "cpr.mm"
include "wo.mm"
include "nn0addcld.mm"
include "m1expcl2.mm"
include "elpri.mm"
include "mpjaod.mm"
include "neg1z.mm"
include "zexpcl.mm"
include "mulcand.mm"
include "3imtr3d.mm"
include "3syld.mm"
include "sylbird.mm"
include "ralrimivva.mm"
include "cmpt.mm"
include "nfmpt1.mm"
include "nfcxfr.mm"
include "nfcv.mm"
include "nffv.mm"
include "nfeq.mm"
include "nfv.mm"
include "nfim.mm"
include "fveq2.mm"
include "equequ2.mm"
include "imbi12d.mm"
include "cbvral.mm"
include "ralbii.mm"
include "sylibr.mm"
include "dff13.mm"
include "sylanbrc.mm"
include "cen.mm"
include "cfn.mm"
include "enref.mm"
include "fzfi.mm"
include "f1finf1o.mm"
include "mp2an.mm"
include "sylib.mm"

theorem lgseisenlem2
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let cP: class P
  let cQ: class Q
  let cR: class R
  let cS: class S
  let cM: class M
  let vk: setvar k
  let cG: class G
  let cL: class L
  let vn: setvar n
  let vu: setvar u
  let vv: setvar v
  let vw: setvar w
  let vz: setvar z
  let cN: class N
  let cY: class Y
  assume lgseisen.1: |- ( ph -> P e. ( Prime \ { 2 } ) )
  assume lgseisen.2: |- ( ph -> Q e. ( Prime \ { 2 } ) )
  assume lgseisen.3: |- ( ph -> P =/= Q )
  assume lgseisen.4: |- R = ( ( Q x. ( 2 x. x ) ) mod P )
  assume lgseisen.5: |- M = ( x e. ( 1 ... ( ( P - 1 ) / 2 ) ) |-> ( ( ( ( -u 1 ^ R ) x. R ) mod P ) / 2 ) )
  assume lgseisen.6: |- S = ( ( Q x. ( 2 x. y ) ) mod P )

  disjoint x y
  disjoint P x
  disjoint P y
  disjoint ph x
  disjoint ph y
  disjoint M y
  disjoint Q x
  disjoint Q y
  disjoint S x
  disjoint k x
  disjoint G k
  disjoint G x
  disjoint L k
  disjoint L x
  disjoint k n
  disjoint k u
  disjoint k v
  disjoint k w
  disjoint k y
  disjoint k z
  disjoint P k
  disjoint n u
  disjoint n v
  disjoint n w
  disjoint n x
  disjoint n y
  disjoint n z
  disjoint P n
  disjoint u v
  disjoint u w
  disjoint u x
  disjoint u y
  disjoint u z
  disjoint P u
  disjoint v w
  disjoint v x
  disjoint v y
  disjoint v z
  disjoint P v
  disjoint w x
  disjoint w y
  disjoint w z
  disjoint P w
  disjoint x z
  disjoint y z
  disjoint P z
  disjoint k ph
  disjoint n ph
  disjoint ph u
  disjoint ph v
  disjoint ph w
  disjoint ph z
  disjoint M n
  disjoint M u
  disjoint M v
  disjoint M w
  disjoint M z
  disjoint N u
  disjoint N w
  disjoint N x
  disjoint N y
  disjoint N z
  disjoint Q k
  disjoint Q u
  disjoint Q w
  disjoint Q z
  disjoint Y k
  disjoint Y x
  disjoint R k
  disjoint S n
  disjoint S u
  disjoint S v
  disjoint S z
  assert |- ( ph -> M : ( 1 ... ( ( P - 1 ) / 2 ) ) -1-1-onto-> ( 1 ... ( ( P - 1 ) / 2 ) ) )

  proof
    wph
    c1
    cP
    c1
    cmin
    co
    #
    c2
    cdiv
    co
    #
    cfz
    co
    #
    @2
    cM
    wf1
    #
    @2
    @2
    cM
    wf1o
    #
    wph
    @2
    @2
    cM
    wf
    vy
    cv
    #
    cM
    cfv
    #
    vz
    cv
    #
    cM
    cfv
    #
    wceq
    #
    vy
    vz
    weq
    #
    wi
    #
    vz
    @2
    wral
    #
    vy
    @2
    wral
    #
    @3
    wph
    vx
    cP
    cQ
    cR
    cM
    lgseisen.1
    lgseisen.2
    lgseisen.3
    lgseisen.4
    lgseisen.5
    lgseisenlem1
    wph
    @6
    vx
    cv
    #
    cM
    cfv
    #
    wceq
    #
    vy
    vx
    weq
    #
    wi
    #
    vx
    @2
    wral
    #
    vy
    @2
    wral
    @13
    wph
    @18
    vy
    vx
    @2
    @2
    wph
    @5
    @2
    wcel
    #
    @14
    @2
    wcel
    #
    wa
    #
    wa
    #
    @16
    c1
    cneg
    #
    cS
    cexp
    co
    #
    cS
    cmul
    co
    #
    cP
    cmo
    co
    #
    c2
    cdiv
    co
    #
    @24
    cR
    cexp
    co
    #
    cR
    cmul
    co
    #
    cP
    cmo
    co
    #
    c2
    cdiv
    co
    #
    wceq
    #
    @17
    @23
    @6
    @28
    @15
    @32
    @20
    @6
    @28
    wceq
    wph
    @21
    vx
    @5
    @32
    @28
    @2
    cM
    vx
    vy
    weq
    #
    @31
    @27
    c2
    cdiv
    @34
    @30
    @26
    cP
    cmo
    @34
    @29
    @25
    cR
    cS
    cmul
    @34
    cR
    cS
    @24
    cexp
    @34
    cQ
    c2
    @14
    cmul
    co
    #
    cmul
    co
    #
    cP
    cmo
    co
    #
    cQ
    c2
    @5
    cmul
    co
    #
    cmul
    co
    #
    cP
    cmo
    co
    #
    cR
    cS
    @34
    @36
    @39
    cP
    cmo
    @34
    @35
    @38
    cQ
    cmul
    @14
    @5
    c2
    cmul
    oveq2
    oveq2d
    oveq1d
    lgseisen.4
    lgseisen.6
    3eqtr4g
    #
    oveq2d
    @41
    oveq12d
    oveq1d
    oveq1d
    lgseisen.5
    @27
    c2
    cdiv
    ovex
    fvmpt
    ad2antrl
    @21
    @15
    @32
    wceq
    #
    wph
    @20
    @21
    @32
    cvv
    wcel
    @42
    @31
    c2
    cdiv
    ovex
    vx
    @2
    @32
    cvv
    cM
    lgseisen.5
    fvmpt2
    mpan2
    ad2antll
    eqeq12d
    @23
    @33
    @27
    @31
    wceq
    #
    @17
    @23
    @27
    cc
    wcel
    @31
    cc
    wcel
    c2
    cc
    wcel
    c2
    cc0
    wne
    #
    @33
    @43
    wb
    @23
    @27
    @23
    @26
    cP
    @23
    @25
    cS
    @23
    cS
    cz
    wcel
    @25
    cz
    wcel
    @23
    cS
    @23
    cS
    @40
    cn0
    lgseisen.6
    @23
    @39
    cP
    @23
    cQ
    @38
    @23
    cQ
    cprime
    wcel
    #
    cQ
    cz
    wcel
    #
    @23
    cQ
    cprime
    c2
    csn
    #
    wph
    cQ
    cprime
    @47
    cdif
    #
    wcel
    @22
    lgseisen.2
    adantr
    eldifad
    #
    cQ
    prmz
    syl
    #
    @23
    c2
    cz
    wcel
    #
    @5
    cz
    wcel
    #
    @38
    cz
    wcel
    #
    2z
    @20
    @52
    wph
    @21
    @5
    c1
    @1
    elfzelz
    ad2antrl
    #
    c2
    @5
    zmulcl
    sylancr
    #
    zmulcld
    #
    @23
    cP
    cprime
    wcel
    #
    cP
    cn
    wcel
    #
    @23
    cP
    cprime
    @47
    wph
    cP
    @48
    wcel
    #
    @22
    lgseisen.1
    adantr
    #
    eldifad
    #
    cP
    prmnn
    syl
    #
    zmodcld
    syl5eqel
    #
    nn0zd
    #
    cS
    m1expcl
    syl
    #
    @64
    zmulcld
    @62
    zmodcld
    nn0cnd
    @23
    @31
    @23
    @30
    cP
    @23
    @29
    cR
    @23
    cR
    cz
    wcel
    @29
    cz
    wcel
    #
    @23
    cR
    @23
    cR
    @37
    cn0
    lgseisen.4
    @23
    @36
    cP
    @23
    cQ
    @35
    @50
    @23
    @51
    @14
    cz
    wcel
    #
    @35
    cz
    wcel
    #
    2z
    @21
    @67
    wph
    @20
    @14
    c1
    @1
    elfzelz
    ad2antll
    #
    c2
    @14
    zmulcl
    sylancr
    #
    zmulcld
    #
    @62
    zmodcld
    syl5eqel
    #
    nn0zd
    #
    cR
    m1expcl
    syl
    #
    @73
    zmulcld
    @62
    zmodcld
    nn0cnd
    @23
    2cnd
    #
    @44
    @23
    2ne0
    a1i
    #
    @27
    @31
    c2
    div11
    syl112anc
    @23
    @43
    @25
    @39
    cmul
    co
    #
    cP
    cmo
    co
    #
    @29
    @36
    cmul
    co
    #
    cP
    cmo
    co
    #
    wceq
    #
    @17
    @23
    @27
    @78
    @31
    @80
    @23
    @25
    @25
    cS
    @39
    cP
    @65
    @65
    @64
    @56
    @23
    cP
    @62
    nnrpd
    #
    @23
    @25
    cP
    cmo
    co
    eqidd
    @23
    cS
    cP
    cmo
    co
    @40
    cP
    cmo
    co
    #
    @40
    cS
    @40
    cP
    cmo
    lgseisen.6
    oveq1i
    @23
    @39
    cr
    wcel
    cP
    crp
    wcel
    #
    @83
    @40
    wceq
    @23
    @39
    @56
    zred
    @82
    @39
    cP
    modabs2
    syl2anc
    syl5eq
    modmul12d
    @23
    @29
    @29
    cR
    @36
    cP
    @74
    @74
    @73
    @71
    @82
    @23
    @29
    cP
    cmo
    co
    eqidd
    @23
    cR
    cP
    cmo
    co
    @37
    cP
    cmo
    co
    #
    @37
    cR
    @37
    cP
    cmo
    lgseisen.4
    oveq1i
    @23
    @36
    cr
    wcel
    @84
    @85
    @37
    wceq
    @23
    @36
    @71
    zred
    @82
    @36
    cP
    modabs2
    syl2anc
    syl5eq
    modmul12d
    eqeq12d
    @23
    @81
    cP
    @77
    @79
    cmin
    co
    #
    cdvds
    wbr
    #
    @17
    @23
    @58
    @77
    cz
    wcel
    @79
    cz
    wcel
    @81
    @87
    wb
    @62
    @23
    @25
    @39
    @65
    @56
    zmulcld
    @23
    @29
    @36
    @74
    @71
    zmulcld
    @77
    @79
    cP
    moddvds
    syl3anc
    @23
    @87
    cP
    cQ
    @25
    @38
    cmul
    co
    #
    @29
    @35
    cmul
    co
    #
    cmin
    co
    #
    cmul
    co
    #
    cdvds
    wbr
    #
    @17
    @23
    @91
    @86
    cP
    cdvds
    @23
    @91
    cQ
    @88
    cmul
    co
    #
    cQ
    @89
    cmul
    co
    #
    cmin
    co
    @86
    @23
    cQ
    @88
    @89
    @23
    cQ
    @50
    zcnd
    #
    @23
    @88
    @23
    @25
    @38
    @65
    @55
    zmulcld
    #
    zcnd
    #
    @23
    @89
    @23
    @29
    @35
    @74
    @70
    zmulcld
    #
    zcnd
    #
    subdid
    @23
    @93
    @77
    @94
    @79
    cmin
    @23
    cQ
    @25
    @38
    @95
    @23
    @25
    @65
    zcnd
    #
    @23
    @38
    @55
    zcnd
    #
    mul12d
    @23
    cQ
    @29
    @35
    @95
    @23
    @29
    @74
    zcnd
    #
    @23
    @35
    @70
    zcnd
    #
    mul12d
    oveq12d
    eqtrd
    breq2d
    @23
    @92
    cP
    @90
    cdvds
    wbr
    #
    cP
    @29
    @90
    cmul
    co
    #
    cdvds
    wbr
    #
    @17
    @23
    @92
    cP
    cQ
    cgcd
    co
    c1
    wceq
    #
    @104
    @23
    @107
    cP
    cQ
    wne
    #
    wph
    @108
    @22
    lgseisen.3
    adantr
    @23
    @57
    @45
    @107
    @108
    wb
    @61
    @49
    cP
    cQ
    prmrp
    syl2anc
    mpbird
    @23
    cP
    cz
    wcel
    #
    @46
    @90
    cz
    wcel
    #
    @92
    @107
    wa
    @104
    wi
    @23
    @57
    @109
    @61
    cP
    prmz
    syl
    #
    @50
    @23
    @88
    @89
    @96
    @98
    zsubcld
    #
    cP
    cQ
    @90
    coprmdvds
    syl3anc
    mpan2d
    @23
    @109
    @66
    @110
    @104
    @106
    wi
    @111
    @74
    @112
    cP
    @29
    @90
    dvdsmultr2
    syl3anc
    @23
    @106
    cP
    @24
    cR
    cS
    caddc
    co
    #
    cexp
    co
    #
    @38
    cmul
    co
    #
    @35
    cmin
    co
    #
    cdvds
    wbr
    #
    @17
    @23
    @105
    @116
    cP
    cdvds
    @23
    @105
    @29
    @88
    cmul
    co
    #
    @29
    @89
    cmul
    co
    #
    cmin
    co
    @116
    @23
    @29
    @88
    @89
    @102
    @97
    @99
    subdid
    @23
    @118
    @115
    @119
    @35
    cmin
    @23
    @115
    @29
    @25
    cmul
    co
    #
    @38
    cmul
    co
    @118
    @23
    @114
    @120
    @38
    cmul
    @23
    @24
    cR
    cS
    @24
    cc
    wcel
    @23
    neg1cn
    a1i
    #
    @63
    @72
    expaddd
    oveq1d
    @23
    @29
    @25
    @38
    @102
    @100
    @101
    mulassd
    eqtr2d
    @23
    @29
    @29
    cmul
    co
    #
    @35
    cmul
    co
    c1
    @35
    cmul
    co
    @119
    @35
    @23
    @122
    c1
    @35
    cmul
    @23
    @122
    @29
    c1
    @29
    cdiv
    co
    #
    cmul
    co
    c1
    @23
    @29
    @123
    @29
    cmul
    @23
    @29
    c1
    @24
    cdiv
    co
    #
    cR
    cexp
    co
    @123
    @124
    @24
    cR
    cexp
    c1
    c1
    cdiv
    co
    #
    cneg
    #
    @124
    @24
    c1
    cc
    wcel
    #
    @127
    c1
    cc0
    wne
    @126
    @124
    wceq
    ax-1cn
    ax-1cn
    ax-1ne0
    c1
    c1
    divneg2
    mp3an
    @125
    c1
    1div1e1
    negeqi
    eqtr3i
    oveq1i
    @23
    @24
    cR
    @121
    @24
    cc0
    wne
    @23
    neg1ne0
    a1i
    #
    @73
    exprecd
    syl5eqr
    oveq2d
    @23
    @29
    @102
    @23
    @24
    cR
    @121
    @128
    @73
    expne0d
    recidd
    eqtrd
    oveq1d
    @23
    @29
    @29
    @35
    @102
    @102
    @103
    mulassd
    @23
    @35
    @103
    mulid2d
    3eqtr3d
    oveq12d
    eqtrd
    breq2d
    @23
    @115
    cP
    cmo
    co
    #
    @35
    cP
    cmo
    co
    #
    wceq
    #
    @38
    @35
    wceq
    #
    @117
    @17
    @23
    @114
    @24
    wceq
    #
    @131
    @132
    wi
    #
    @114
    c1
    wceq
    #
    @23
    @134
    @133
    @24
    @38
    cmul
    co
    #
    cP
    cmo
    co
    #
    @130
    wceq
    #
    @132
    wi
    @23
    @138
    @130
    @38
    cneg
    #
    cP
    cmo
    co
    #
    wceq
    #
    @132
    @138
    @130
    @137
    wceq
    @23
    @141
    @137
    @130
    eqcom
    @23
    @137
    @140
    @130
    @23
    @136
    @139
    cP
    cmo
    @23
    @38
    @101
    mulm1d
    oveq1d
    eqeq2d
    syl5bb
    @23
    @141
    cP
    @35
    @139
    cmin
    co
    #
    cdvds
    wbr
    #
    @132
    @23
    @58
    @68
    @139
    cz
    wcel
    @141
    @143
    wb
    @62
    @70
    @23
    @38
    @55
    znegcld
    @35
    @139
    cP
    moddvds
    syl3anc
    @23
    @143
    @132
    @23
    @143
    cP
    c2
    @14
    @5
    caddc
    co
    #
    cmul
    co
    #
    cdvds
    wbr
    #
    @23
    @146
    cP
    @144
    cdvds
    wbr
    #
    @23
    @58
    @144
    c1
    @0
    cfz
    co
    wcel
    #
    @147
    wn
    @62
    @23
    @148
    @144
    cn
    wcel
    #
    @144
    @0
    cle
    wbr
    #
    @23
    @14
    @5
    @21
    @14
    cn
    wcel
    #
    wph
    @20
    @14
    @1
    elfznn
    ad2antll
    #
    @20
    @5
    cn
    wcel
    #
    wph
    @21
    @5
    @1
    elfznn
    ad2antrl
    #
    nnaddcld
    #
    @23
    @144
    @1
    @1
    caddc
    co
    @0
    cle
    @23
    @14
    @5
    @1
    @1
    @23
    @14
    @152
    nnred
    #
    @23
    @5
    @54
    zred
    #
    @23
    @1
    @23
    @59
    @1
    cn
    wcel
    @60
    cP
    oddprm
    syl
    nnred
    #
    @158
    @21
    @14
    @1
    cle
    wbr
    #
    wph
    @20
    @14
    c1
    @1
    elfzle2
    ad2antll
    #
    @20
    @5
    @1
    cle
    wbr
    #
    wph
    @21
    @5
    c1
    @1
    elfzle2
    ad2antrl
    #
    le2addd
    @23
    @0
    @23
    @0
    @23
    cP
    cr
    wcel
    @0
    cr
    wcel
    #
    @23
    cP
    @62
    nnred
    cP
    peano2rem
    syl
    #
    recnd
    2halvesd
    breqtrd
    @23
    @109
    @0
    cz
    wcel
    @148
    @149
    @150
    wa
    wb
    @111
    cP
    peano2zm
    @144
    @0
    fznn
    3syl
    mpbir2and
    cP
    @144
    fzm1ndvds
    syl2anc
    @23
    @146
    cP
    c2
    cgcd
    co
    c1
    wceq
    #
    @147
    @23
    @165
    cP
    c2
    wne
    #
    @23
    @59
    @166
    @60
    cP
    cprime
    c2
    eldifsni
    syl
    @23
    @57
    c2
    cprime
    wcel
    @165
    @166
    wb
    @61
    2prm
    cP
    c2
    prmrp
    sylancl
    mpbird
    @23
    @109
    @51
    @144
    cz
    wcel
    @146
    @165
    wa
    @147
    wi
    @111
    @51
    @23
    2z
    a1i
    @23
    @144
    @155
    nnzd
    cP
    c2
    @144
    coprmdvds
    syl3anc
    mpan2d
    mtod
    @23
    @142
    @145
    cP
    cdvds
    @23
    @142
    @35
    @38
    caddc
    co
    @145
    @23
    @35
    @38
    @103
    @101
    subnegd
    @23
    c2
    @14
    @5
    @75
    @23
    @14
    @69
    zcnd
    #
    @23
    @5
    @54
    zcnd
    #
    adddid
    eqtr4d
    breq2d
    mtbird
    pm2.21d
    sylbid
    sylbid
    @133
    @131
    @138
    @132
    @133
    @129
    @137
    @130
    @133
    @115
    @136
    cP
    cmo
    @114
    @24
    @38
    cmul
    oveq1
    oveq1d
    eqeq1d
    imbi1d
    syl5ibrcom
    @23
    @134
    @135
    c1
    @38
    cmul
    co
    #
    cP
    cmo
    co
    #
    @130
    wceq
    #
    @132
    wi
    @23
    @171
    @132
    @23
    @170
    @38
    @130
    @35
    @23
    @170
    @38
    cP
    cmo
    co
    #
    @38
    @23
    @169
    @38
    cP
    cmo
    @23
    @38
    @101
    mulid2d
    oveq1d
    @23
    @38
    cr
    wcel
    @84
    cc0
    @38
    cle
    wbr
    @38
    cP
    clt
    wbr
    #
    @172
    @38
    wceq
    @23
    @38
    @55
    zred
    @82
    @23
    @38
    @23
    @38
    @23
    c2
    cn
    wcel
    #
    @153
    @38
    cn
    wcel
    2nn
    @154
    c2
    @5
    nnmulcl
    sylancr
    nnnn0d
    nn0ge0d
    @23
    @173
    @38
    @0
    cle
    wbr
    #
    @23
    @175
    @161
    @162
    @23
    @5
    cr
    wcel
    @163
    c2
    cr
    wcel
    #
    cc0
    c2
    clt
    wbr
    #
    @175
    @161
    wb
    @157
    @164
    @176
    @23
    2re
    a1i
    #
    @177
    @23
    2pos
    a1i
    #
    @5
    @0
    c2
    lemuldiv2
    syl112anc
    mpbird
    @23
    @53
    @109
    @173
    @175
    wb
    @55
    @111
    @38
    cP
    zltlem1
    syl2anc
    mpbird
    @38
    cP
    modid
    syl22anc
    eqtrd
    @23
    @35
    cr
    wcel
    @84
    cc0
    @35
    cle
    wbr
    @35
    cP
    clt
    wbr
    #
    @130
    @35
    wceq
    @23
    @35
    @70
    zred
    @82
    @23
    @35
    @23
    @35
    @23
    @174
    @151
    @35
    cn
    wcel
    2nn
    @152
    c2
    @14
    nnmulcl
    sylancr
    nnnn0d
    nn0ge0d
    @23
    @180
    @35
    @0
    cle
    wbr
    #
    @23
    @181
    @159
    @160
    @23
    @14
    cr
    wcel
    @163
    @176
    @177
    @181
    @159
    wb
    @156
    @164
    @178
    @179
    @14
    @0
    c2
    lemuldiv2
    syl112anc
    mpbird
    @23
    @68
    @109
    @180
    @181
    wb
    @70
    @111
    @35
    cP
    zltlem1
    syl2anc
    mpbird
    @35
    cP
    modid
    syl22anc
    eqeq12d
    biimpd
    @135
    @131
    @171
    @132
    @135
    @129
    @170
    @130
    @135
    @115
    @169
    cP
    cmo
    @114
    c1
    @38
    cmul
    oveq1
    oveq1d
    eqeq1d
    imbi1d
    syl5ibrcom
    @23
    @113
    cz
    wcel
    @114
    @24
    c1
    cpr
    wcel
    @133
    @135
    wo
    @23
    @113
    @23
    cR
    cS
    @72
    @63
    nn0addcld
    #
    nn0zd
    @113
    m1expcl2
    @114
    @24
    c1
    elpri
    3syl
    mpjaod
    @23
    @58
    @115
    cz
    wcel
    @68
    @131
    @117
    wb
    @62
    @23
    @114
    @38
    @23
    @24
    cz
    wcel
    @113
    cn0
    wcel
    @114
    cz
    wcel
    neg1z
    @182
    @24
    @113
    zexpcl
    sylancr
    @55
    zmulcld
    @70
    @115
    @35
    cP
    moddvds
    syl3anc
    @23
    @5
    @14
    c2
    @168
    @167
    @75
    @76
    mulcand
    3imtr3d
    sylbid
    3syld
    sylbird
    sylbid
    sylbid
    sylbid
    sylbid
    ralrimivva
    @12
    @19
    vy
    @2
    @11
    @18
    vz
    vx
    @2
    @9
    @10
    vx
    vx
    @6
    @8
    vx
    @5
    cM
    vx
    cM
    vx
    @2
    @32
    cmpt
    lgseisen.5
    vx
    @2
    @32
    nfmpt1
    nfcxfr
    #
    vx
    @5
    nfcv
    nffv
    vx
    @7
    cM
    @183
    vx
    @7
    nfcv
    nffv
    nfeq
    @10
    vx
    nfv
    nfim
    @18
    vz
    nfv
    vz
    vx
    weq
    #
    @9
    @16
    @10
    @17
    @184
    @8
    @15
    @6
    @7
    @14
    cM
    fveq2
    eqeq2d
    vz
    vx
    vy
    equequ2
    imbi12d
    cbvral
    ralbii
    sylibr
    vy
    vz
    @2
    @2
    cM
    dff13
    sylanbrc
    @2
    @2
    cen
    wbr
    @2
    cfn
    wcel
    @3
    @4
    wb
    @2
    c1
    @1
    cfz
    ovex
    enref
    c1
    @1
    fzfi
    @2
    @2
    cM
    f1finf1o
    mp2an
    sylib
end
