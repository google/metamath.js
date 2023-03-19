include "c1.mm"
include "cmin.mm"
include "co.mm"
include "c2.mm"
include "cdiv.mm"
include "cfz.mm"
include "cneg.mm"
include "cexp.mm"
include "cmul.mm"
include "cmo.mm"
include "cv.mm"
include "wcel.mm"
include "wa.mm"
include "cle.mm"
include "wbr.mm"
include "cz.mm"
include "cc0.mm"
include "clt.mm"
include "cn.mm"
include "caddc.mm"
include "cc.mm"
include "wne.mm"
include "wceq.mm"
include "neg1cn.mm"
include "a1i.mm"
include "neg1ne0.mm"
include "2z.mm"
include "simpr.mm"
include "expmulz.mm"
include "syl22anc.mm"
include "cn0.mm"
include "cprime.mm"
include "csn.mm"
include "cdif.mm"
include "adantr.mm"
include "eldifad.mm"
include "prmz.mm"
include "syl.mm"
include "elfzelz.mm"
include "adantl.mm"
include "zmulcl.mm"
include "sylancr.mm"
include "zmulcld.mm"
include "prmnn.mm"
include "zmodfz.mm"
include "syl2anc.mm"
include "syl5eqel.mm"
include "elfznn0.mm"
include "nn0zd.mm"
include "zcnd.mm"
include "2cnd.mm"
include "2ne0.mm"
include "divcan2d.mm"
include "oveq2d.mm"
include "neg1sqe1.mm"
include "oveq1i.mm"
include "1exp.mm"
include "syl5eq.mm"
include "3eqtr3d.mm"
include "oveq1d.mm"
include "mulid2d.mm"
include "eqtrd.mm"
include "cr.mm"
include "crp.mm"
include "nn0red.mm"
include "nnrpd.mm"
include "nn0ge0d.mm"
include "zred.mm"
include "modlt.mm"
include "syl5eqbr.mm"
include "modid.mm"
include "eqeltrd.mm"
include "nncnd.mm"
include "renegcld.mm"
include "recnd.mm"
include "addcomd.mm"
include "negsubd.mm"
include "3eqtr2d.mm"
include "1zzd.mm"
include "modcyc.mm"
include "syl3anc.mm"
include "nnred.mm"
include "resubcld.mm"
include "ltled.mm"
include "subge0d.mm"
include "mpbird.mm"
include "wn.mm"
include "cdvds.mm"
include "2nn.mm"
include "elfznn.mm"
include "nnmulcl.mm"
include "elfzle2.mm"
include "wb.mm"
include "cuz.mm"
include "cfv.mm"
include "prmuz2.mm"
include "uz2m1nn.mm"
include "3syl.mm"
include "2re.mm"
include "2pos.mm"
include "lemuldiv2.mm"
include "syl112anc.mm"
include "peano2zm.mm"
include "fznn.mm"
include "mpbir2and.mm"
include "fzm1ndvds.mm"
include "cgcd.mm"
include "prmrp.mm"
include "wi.mm"
include "coprmdvds.mm"
include "mpan2d.mm"
include "mtod.mm"
include "dvdsval3.mm"
include "mtbid.mm"
include "eqeq1i.mm"
include "sylnibr.mm"
include "wo.mm"
include "nnnn0d.mm"
include "nn0uz.mm"
include "syl6eleq.mm"
include "elfzp12.mm"
include "mpbid.mm"
include "ord.mm"
include "mpd.mm"
include "1e0p1.mm"
include "syl6eleqr.mm"
include "ltsubrpd.mm"
include "ax-1cn.mm"
include "peano2zd.mm"
include "dvdsval2.mm"
include "biimpar.mm"
include "1lt2.mm"
include "ndvdsp1.mm"
include "mt2d.mm"
include "oexpneg.mm"
include "negeqd.mm"
include "mulm1d.mm"
include "pnpcan2d.mm"
include "3eqtr4d.mm"
include "peano2cn.mm"
include "divsubdird.mm"
include "subadd23d.mm"
include "2m1e1.mm"
include "oveq2i.mm"
include "syl6req.mm"
include "divdird.mm"
include "2div2e1.mm"
include "syl6eq.mm"
include "oddprm.mm"
include "nnzd.mm"
include "zsubcld.mm"
include "zeo.mm"
include "mpjaodan.mm"
include "m1expcl.mm"
include "zmodcld.mm"
include "ax-1ne0.mm"
include "divneg2.mm"
include "mp3an.mm"
include "1div1e1.mm"
include "negeqi.mm"
include "eqtr3i.mm"
include "exprecd.mm"
include "syl5eqr.mm"
include "expne0d.mm"
include "recidd.mm"
include "mulassd.mm"
include "breq2d.mm"
include "mtbird.mm"
include "dvdsmultr2.mm"
include "elnn0.mm"
include "sylib.mm"
include "mt3d.mm"
include "nngt0d.mm"
include "divgt0d.mm"
include "elnnz.mm"
include "sylanbrc.mm"
include "nnge1d.mm"
include "lediv1.mm"
include "elfz.mm"
include "fmptd.mm"

theorem lgseisenlem1
  let wph: wff ph
  let vx: setvar x
  let cP: class P
  let cQ: class Q
  let cR: class R
  let cM: class M
  let vk: setvar k
  let cG: class G
  let cL: class L
  let vn: setvar n
  let vu: setvar u
  let vv: setvar v
  let vw: setvar w
  let vy: setvar y
  let vz: setvar z
  let cN: class N
  let cY: class Y
  let cS: class S
  assume lgseisen.1: |- ( ph -> P e. ( Prime \ { 2 } ) )
  assume lgseisen.2: |- ( ph -> Q e. ( Prime \ { 2 } ) )
  assume lgseisen.3: |- ( ph -> P =/= Q )
  assume lgseisen.4: |- R = ( ( Q x. ( 2 x. x ) ) mod P )
  assume lgseisen.5: |- M = ( x e. ( 1 ... ( ( P - 1 ) / 2 ) ) |-> ( ( ( ( -u 1 ^ R ) x. R ) mod P ) / 2 ) )

  disjoint P x
  disjoint ph x
  disjoint Q x
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
  disjoint x y
  disjoint x z
  disjoint y z
  disjoint P y
  disjoint P z
  disjoint k ph
  disjoint n ph
  disjoint ph u
  disjoint ph v
  disjoint ph w
  disjoint ph y
  disjoint ph z
  disjoint M n
  disjoint M u
  disjoint M v
  disjoint M w
  disjoint M y
  disjoint M z
  disjoint N u
  disjoint N w
  disjoint N x
  disjoint N y
  disjoint N z
  disjoint Q k
  disjoint Q u
  disjoint Q w
  disjoint Q y
  disjoint Q z
  disjoint Y k
  disjoint Y x
  disjoint R k
  disjoint S n
  disjoint S u
  disjoint S v
  disjoint S x
  disjoint S z
  assert |- ( ph -> M : ( 1 ... ( ( P - 1 ) / 2 ) ) --> ( 1 ... ( ( P - 1 ) / 2 ) ) )

  proof
    wph
    vx
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
    c1
    cneg
    #
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
    @2
    cM
    wph
    vx
    cv
    #
    @2
    wcel
    #
    wa
    #
    @7
    @2
    wcel
    #
    c1
    @7
    cle
    wbr
    #
    @7
    @1
    cle
    wbr
    #
    @10
    @7
    @10
    @7
    cz
    wcel
    #
    cc0
    @7
    clt
    wbr
    @7
    cn
    wcel
    @10
    cR
    c2
    cdiv
    co
    #
    cz
    wcel
    #
    @14
    cR
    c1
    caddc
    co
    #
    c2
    cdiv
    co
    #
    cz
    wcel
    #
    @10
    @16
    wa
    #
    @7
    @15
    cz
    @20
    @6
    cR
    c2
    cdiv
    @20
    @6
    cR
    cP
    cmo
    co
    #
    cR
    @20
    @5
    cR
    cP
    cmo
    @20
    @5
    c1
    cR
    cmul
    co
    #
    cR
    @20
    @4
    c1
    cR
    cmul
    @20
    @3
    c2
    @15
    cmul
    co
    #
    cexp
    co
    #
    @3
    c2
    cexp
    co
    #
    @15
    cexp
    co
    #
    @4
    c1
    @20
    @3
    cc
    wcel
    #
    @3
    cc0
    wne
    #
    c2
    cz
    wcel
    #
    @16
    @24
    @26
    wceq
    @27
    @20
    neg1cn
    a1i
    @28
    @20
    neg1ne0
    a1i
    @29
    @20
    2z
    a1i
    @10
    @16
    simpr
    #
    @3
    c2
    @15
    expmulz
    syl22anc
    @20
    @23
    cR
    @3
    cexp
    @20
    cR
    c2
    @10
    cR
    cc
    wcel
    #
    @16
    @10
    cR
    @10
    cR
    @10
    cR
    cc0
    @0
    cfz
    co
    #
    wcel
    #
    cR
    cn0
    wcel
    @10
    cR
    cQ
    c2
    @8
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
    @32
    lgseisen.4
    @10
    @35
    cz
    wcel
    #
    cP
    cn
    wcel
    #
    @36
    @32
    wcel
    @10
    cQ
    @34
    @10
    cQ
    cprime
    wcel
    #
    cQ
    cz
    wcel
    #
    @10
    cQ
    cprime
    c2
    csn
    #
    wph
    cQ
    cprime
    @41
    cdif
    #
    wcel
    @9
    lgseisen.2
    adantr
    eldifad
    #
    cQ
    prmz
    syl
    #
    @10
    @29
    @8
    cz
    wcel
    #
    @34
    cz
    wcel
    #
    2z
    @9
    @45
    wph
    @8
    c1
    @1
    elfzelz
    adantl
    c2
    @8
    zmulcl
    sylancr
    #
    zmulcld
    #
    @10
    cP
    cprime
    wcel
    #
    @38
    @10
    cP
    cprime
    @41
    wph
    cP
    @42
    wcel
    #
    @9
    lgseisen.1
    adantr
    #
    eldifad
    #
    cP
    prmnn
    syl
    #
    @35
    cP
    zmodfz
    syl2anc
    syl5eqel
    #
    cR
    @0
    elfznn0
    syl
    #
    nn0zd
    #
    zcnd
    #
    adantr
    #
    @20
    2cnd
    c2
    cc0
    wne
    #
    @20
    2ne0
    a1i
    divcan2d
    oveq2d
    @20
    @26
    c1
    @15
    cexp
    co
    #
    c1
    @25
    c1
    @15
    cexp
    neg1sqe1
    oveq1i
    @16
    @60
    c1
    wceq
    @10
    @15
    1exp
    adantl
    syl5eq
    3eqtr3d
    oveq1d
    @20
    cR
    @58
    mulid2d
    eqtrd
    oveq1d
    @10
    @21
    cR
    wceq
    #
    @16
    @10
    cR
    cr
    wcel
    cP
    crp
    wcel
    #
    cc0
    cR
    cle
    wbr
    cR
    cP
    clt
    wbr
    @61
    @10
    cR
    @55
    nn0red
    #
    @10
    cP
    @53
    nnrpd
    #
    @10
    cR
    @55
    nn0ge0d
    @10
    cR
    @36
    cP
    clt
    lgseisen.4
    @10
    @35
    cr
    wcel
    @62
    @36
    cP
    clt
    wbr
    @10
    @35
    @48
    zred
    @64
    @35
    cP
    modlt
    syl2anc
    syl5eqbr
    #
    cR
    cP
    modid
    syl22anc
    adantr
    eqtrd
    oveq1d
    @30
    eqeltrd
    @10
    @19
    wa
    #
    @7
    cP
    c1
    caddc
    co
    #
    c2
    cdiv
    co
    #
    @18
    cmin
    co
    #
    cz
    @66
    @7
    @67
    @17
    cmin
    co
    #
    c2
    cdiv
    co
    @69
    @66
    @6
    @70
    c2
    cdiv
    @66
    cR
    cneg
    #
    cP
    cmo
    co
    #
    cP
    cR
    cmin
    co
    #
    @6
    @70
    @10
    @72
    @73
    wceq
    @19
    @10
    @71
    c1
    cP
    cmul
    co
    #
    caddc
    co
    #
    cP
    cmo
    co
    #
    @73
    cP
    cmo
    co
    #
    @72
    @73
    @10
    @75
    @73
    cP
    cmo
    @10
    @75
    @71
    cP
    caddc
    co
    cP
    @71
    caddc
    co
    @73
    @10
    @74
    cP
    @71
    caddc
    @10
    cP
    @10
    cP
    @53
    nncnd
    #
    mulid2d
    oveq2d
    @10
    cP
    @71
    @78
    @10
    @71
    @10
    cR
    @63
    renegcld
    #
    recnd
    addcomd
    @10
    cP
    cR
    @78
    @57
    negsubd
    3eqtr2d
    oveq1d
    @10
    @71
    cr
    wcel
    @62
    c1
    cz
    wcel
    #
    @76
    @72
    wceq
    @79
    @64
    @10
    1zzd
    #
    @71
    cP
    c1
    modcyc
    syl3anc
    @10
    @73
    cr
    wcel
    @62
    cc0
    @73
    cle
    wbr
    #
    @73
    cP
    clt
    wbr
    @77
    @73
    wceq
    @10
    cP
    cR
    @10
    cP
    @53
    nnred
    #
    @63
    resubcld
    @64
    @10
    @82
    cR
    cP
    cle
    wbr
    @10
    cR
    cP
    @63
    @83
    @65
    ltled
    @10
    cP
    cR
    @83
    @63
    subge0d
    mpbird
    @10
    cP
    cR
    @83
    @10
    cR
    @10
    cR
    c1
    @0
    cfz
    co
    #
    wcel
    #
    cR
    cn
    wcel
    #
    @10
    cR
    cc0
    c1
    caddc
    co
    #
    @0
    cfz
    co
    #
    @84
    @10
    cR
    cc0
    wceq
    #
    wn
    cR
    @88
    wcel
    #
    @10
    @36
    cc0
    wceq
    #
    @89
    @10
    cP
    @35
    cdvds
    wbr
    #
    @91
    @10
    @92
    cP
    @34
    cdvds
    wbr
    #
    @10
    @38
    @34
    @84
    wcel
    #
    @93
    wn
    @53
    @10
    @94
    @34
    cn
    wcel
    #
    @34
    @0
    cle
    wbr
    #
    @10
    c2
    cn
    wcel
    #
    @8
    cn
    wcel
    #
    @95
    2nn
    @9
    @98
    wph
    @8
    @1
    elfznn
    adantl
    #
    c2
    @8
    nnmulcl
    sylancr
    @10
    @96
    @8
    @1
    cle
    wbr
    #
    @9
    @100
    wph
    @8
    c1
    @1
    elfzle2
    adantl
    @10
    @8
    cr
    wcel
    @0
    cr
    wcel
    #
    c2
    cr
    wcel
    #
    cc0
    c2
    clt
    wbr
    #
    @96
    @100
    wb
    @10
    @8
    @99
    nnred
    @10
    @0
    @10
    @49
    cP
    c2
    cuz
    cfv
    wcel
    @0
    cn
    wcel
    @52
    cP
    prmuz2
    cP
    uz2m1nn
    3syl
    #
    nnred
    #
    @102
    @10
    2re
    a1i
    #
    @103
    @10
    2pos
    a1i
    #
    @8
    @0
    c2
    lemuldiv2
    syl112anc
    mpbird
    @10
    cP
    cz
    wcel
    #
    @0
    cz
    wcel
    @94
    @95
    @96
    wa
    wb
    @10
    @49
    @108
    @52
    cP
    prmz
    syl
    #
    cP
    peano2zm
    @34
    @0
    fznn
    3syl
    mpbir2and
    cP
    @34
    fzm1ndvds
    syl2anc
    @10
    @92
    cP
    cQ
    cgcd
    co
    c1
    wceq
    #
    @93
    @10
    @110
    cP
    cQ
    wne
    #
    wph
    @111
    @9
    lgseisen.3
    adantr
    @10
    @49
    @39
    @110
    @111
    wb
    @52
    @43
    cP
    cQ
    prmrp
    syl2anc
    mpbird
    @10
    @108
    @40
    @46
    @92
    @110
    wa
    @93
    wi
    @109
    @44
    @47
    cP
    cQ
    @34
    coprmdvds
    syl3anc
    mpan2d
    mtod
    @10
    @38
    @37
    @92
    @91
    wb
    @53
    @48
    cP
    @35
    dvdsval3
    syl2anc
    mtbid
    cR
    @36
    cc0
    lgseisen.4
    eqeq1i
    sylnibr
    @10
    @89
    @90
    @10
    @33
    @89
    @90
    wo
    #
    @54
    @10
    @0
    cc0
    cuz
    cfv
    #
    wcel
    @33
    @112
    wb
    @10
    @0
    cn0
    @113
    @10
    @0
    @104
    nnnn0d
    nn0uz
    syl6eleq
    cR
    cc0
    @0
    elfzp12
    syl
    mpbid
    ord
    mpd
    c1
    @87
    @0
    cfz
    1e0p1
    oveq1i
    syl6eleqr
    #
    cR
    @0
    elfznn
    syl
    #
    nnrpd
    ltsubrpd
    @73
    cP
    modid
    syl22anc
    3eqtr3d
    adantr
    @66
    @5
    @71
    cP
    cmo
    @66
    @5
    @3
    cR
    cmul
    co
    @71
    @66
    @4
    @3
    cR
    cmul
    @66
    @4
    c1
    cR
    cexp
    co
    #
    cneg
    #
    @3
    @66
    c1
    cc
    wcel
    #
    @86
    c2
    cR
    cdvds
    wbr
    #
    wn
    @4
    @117
    wceq
    @118
    @66
    ax-1cn
    a1i
    #
    @10
    @86
    @19
    @115
    adantr
    @66
    @119
    c2
    @17
    cdvds
    wbr
    #
    @10
    @121
    @19
    @10
    @29
    @59
    @17
    cz
    wcel
    @121
    @19
    wb
    @29
    @10
    2z
    a1i
    @59
    @10
    2ne0
    a1i
    @10
    cR
    @56
    peano2zd
    c2
    @17
    dvdsval2
    syl3anc
    biimpar
    @66
    cR
    cz
    wcel
    #
    @97
    c1
    c2
    clt
    wbr
    #
    @119
    @121
    wn
    wi
    @10
    @122
    @19
    @56
    adantr
    #
    @97
    @66
    2nn
    a1i
    @123
    @66
    1lt2
    a1i
    c2
    cR
    ndvdsp1
    syl3anc
    mt2d
    c1
    cR
    oexpneg
    syl3anc
    @66
    @116
    c1
    @66
    @122
    @116
    c1
    wceq
    @124
    cR
    1exp
    syl
    negeqd
    eqtrd
    oveq1d
    @66
    cR
    @10
    @31
    @19
    @57
    adantr
    #
    mulm1d
    eqtrd
    oveq1d
    @66
    cP
    cR
    c1
    @10
    cP
    cc
    wcel
    #
    @19
    @78
    adantr
    #
    @125
    @120
    pnpcan2d
    3eqtr4d
    oveq1d
    @66
    @67
    @17
    c2
    @66
    @126
    @67
    cc
    wcel
    @127
    cP
    peano2cn
    syl
    @66
    @31
    @17
    cc
    wcel
    @125
    cR
    peano2cn
    syl
    @66
    2cnd
    #
    @59
    @66
    2ne0
    a1i
    #
    divsubdird
    eqtrd
    @66
    @68
    @18
    @66
    @68
    @1
    c1
    caddc
    co
    #
    cz
    @66
    @68
    @0
    c2
    caddc
    co
    #
    c2
    cdiv
    co
    #
    @130
    @66
    @67
    @131
    c2
    cdiv
    @66
    @131
    cP
    c2
    c1
    cmin
    co
    #
    caddc
    co
    @67
    @66
    cP
    c1
    c2
    @127
    @120
    @128
    subadd23d
    @133
    c1
    cP
    caddc
    2m1e1
    oveq2i
    syl6req
    oveq1d
    @66
    @132
    @1
    c2
    c2
    cdiv
    co
    #
    caddc
    co
    @130
    @66
    @0
    c2
    c2
    @10
    @0
    cc
    wcel
    @19
    @10
    @0
    @104
    nncnd
    adantr
    @128
    @128
    @129
    divdird
    @134
    c1
    @1
    caddc
    2div2e1
    oveq2i
    syl6eq
    eqtrd
    @66
    @1
    @10
    @1
    cz
    wcel
    #
    @19
    @10
    @1
    @10
    @50
    @1
    cn
    wcel
    @51
    cP
    oddprm
    syl
    nnzd
    #
    adantr
    peano2zd
    eqeltrd
    @10
    @19
    simpr
    zsubcld
    eqeltrd
    @10
    @122
    @16
    @19
    wo
    @56
    cR
    zeo
    syl
    mpjaodan
    #
    @10
    @6
    c2
    @10
    @6
    @10
    @5
    cP
    @10
    @4
    cR
    @10
    @122
    @4
    cz
    wcel
    #
    @56
    cR
    m1expcl
    syl
    #
    @56
    zmulcld
    #
    @53
    zmodcld
    #
    nn0red
    #
    @106
    @10
    @6
    @10
    @6
    cn
    wcel
    #
    @6
    cc0
    wceq
    #
    @10
    cP
    @5
    cdvds
    wbr
    #
    @144
    @10
    @145
    cP
    @4
    @5
    cmul
    co
    #
    cdvds
    wbr
    #
    @10
    @147
    cP
    cR
    cdvds
    wbr
    #
    @10
    @38
    @85
    @148
    wn
    @53
    @114
    cP
    cR
    fzm1ndvds
    syl2anc
    @10
    @146
    cR
    cP
    cdvds
    @10
    @4
    @4
    cmul
    co
    #
    cR
    cmul
    co
    @22
    @146
    cR
    @10
    @149
    c1
    cR
    cmul
    @10
    @149
    @4
    c1
    @4
    cdiv
    co
    #
    cmul
    co
    c1
    @10
    @4
    @150
    @4
    cmul
    @10
    @4
    c1
    @3
    cdiv
    co
    #
    cR
    cexp
    co
    @150
    @151
    @3
    cR
    cexp
    c1
    c1
    cdiv
    co
    #
    cneg
    #
    @151
    @3
    @118
    @118
    c1
    cc0
    wne
    @153
    @151
    wceq
    ax-1cn
    ax-1cn
    ax-1ne0
    c1
    c1
    divneg2
    mp3an
    @152
    c1
    1div1e1
    negeqi
    eqtr3i
    oveq1i
    @10
    @3
    cR
    @27
    @10
    neg1cn
    a1i
    #
    @28
    @10
    neg1ne0
    a1i
    #
    @56
    exprecd
    syl5eqr
    oveq2d
    @10
    @4
    @10
    @4
    @139
    zcnd
    #
    @10
    @3
    cR
    @154
    @155
    @56
    expne0d
    recidd
    eqtrd
    oveq1d
    @10
    @4
    @4
    cR
    @156
    @156
    @57
    mulassd
    @10
    cR
    @57
    mulid2d
    3eqtr3d
    breq2d
    mtbird
    @10
    @108
    @138
    @5
    cz
    wcel
    #
    @145
    @147
    wi
    @109
    @139
    @140
    cP
    @4
    @5
    dvdsmultr2
    syl3anc
    mtod
    @10
    @38
    @157
    @145
    @144
    wb
    @53
    @140
    cP
    @5
    dvdsval3
    syl2anc
    mtbid
    @10
    @143
    @144
    @10
    @6
    cn0
    wcel
    @143
    @144
    wo
    @141
    @6
    elnn0
    sylib
    ord
    mt3d
    nngt0d
    @107
    divgt0d
    @7
    elnnz
    sylanbrc
    nnge1d
    @10
    @6
    @0
    cle
    wbr
    #
    @13
    @10
    @6
    @32
    wcel
    #
    @158
    @10
    @157
    @38
    @159
    @140
    @53
    @5
    cP
    zmodfz
    syl2anc
    @6
    cc0
    @0
    elfzle2
    syl
    @10
    @6
    cr
    wcel
    @101
    @102
    @103
    @158
    @13
    wb
    @142
    @105
    @106
    @107
    @6
    @0
    c2
    lediv1
    syl112anc
    mpbid
    @10
    @14
    @80
    @135
    @11
    @12
    @13
    wa
    wb
    @137
    @81
    @136
    @7
    c1
    @1
    elfz
    syl3anc
    mpbir2and
    lgseisen.5
    fmptd
end
