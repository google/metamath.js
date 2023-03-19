include "cfv.mm"
include "cioo.mm"
include "crn.mm"
include "ctg.mm"
include "ccnp.mm"
include "co.mm"
include "wcel.mm"
include "cres.mm"
include "crest.mm"
include "ccnfld.mm"
include "ctopn.mm"
include "cr.mm"
include "cv.mm"
include "wral.mm"
include "cc.mm"
include "wf.mm"
include "ccn.mm"
include "wa.mm"
include "c1.mm"
include "c2.mm"
include "cdiv.mm"
include "caddc.mm"
include "cmul.mm"
include "csin.mm"
include "cpi.mm"
include "cmpt.mm"
include "ccncf.mm"
include "sincn.mm"
include "a1i.mm"
include "wss.mm"
include "ioosscn.mm"
include "nncnd.mm"
include "1cnd.mm"
include "halfcld.mm"
include "addcld.mm"
include "ssid.mm"
include "constcncfg.mm"
include "idcncfg.mm"
include "mulcncf.mm"
include "cncfmpt1f.mm"
include "cc0.mm"
include "csn.mm"
include "cdif.mm"
include "ccom.mm"
include "2cnd.mm"
include "crp.mm"
include "pirp.mm"
include "rpcnd.mm"
include "mulcld.mm"
include "ioossre.mm"
include "sselda.mm"
include "recnd.mm"
include "sincld.mm"
include "wceq.mm"
include "2rp.mm"
include "rpne0d.mm"
include "mulne0d.mm"
include "cz.mm"
include "divdiv1d.mm"
include "clt.mm"
include "wbr.mm"
include "wn.mm"
include "cfl.mm"
include "oveq1i.mm"
include "eqtri.mm"
include "2re.mm"
include "pire.mm"
include "remulcli.mm"
include "wne.mm"
include "0re.mm"
include "2pos.mm"
include "pipos.mm"
include "mulgt0ii.mm"
include "gtneii.mm"
include "redivcld.mm"
include "flcld.mm"
include "zred.mm"
include "divcan4d.mm"
include "syl5eq.mm"
include "eqeltrd.mm"
include "adantr.mm"
include "remulcld.mm"
include "syl5eqel.mm"
include "rpmulcld.mm"
include "w3a.mm"
include "simpr.mm"
include "cxr.mm"
include "wb.mm"
include "rexrd.mm"
include "eqcomi.mm"
include "eqtr4i.mm"
include "1red.mm"
include "readdcld.mm"
include "eqeltrrd.mm"
include "elioo2.mm"
include "syl2anc.mm"
include "mpbid.mm"
include "simp2d.mm"
include "ltdiv1dd.mm"
include "simp3d.mm"
include "oveq1d.mm"
include "eqtr2d.mm"
include "3eqtrrd.mm"
include "breqtrd.mm"
include "btwnnz.mm"
include "syl3anc.mm"
include "eqneltrd.mm"
include "sineq0.mm"
include "syl.mm"
include "mtbird.mm"
include "neqned.mm"
include "neneqd.mm"
include "rehalfcld.mm"
include "resincld.mm"
include "elsng.mm"
include "eldifd.mm"
include "eqidd.mm"
include "oveq2.mm"
include "fmptco.mm"
include "eqid.mm"
include "divrecd.mm"
include "mpteq2dva.mm"
include "difssd.mm"
include "cncfmptssg.mm"
include "ax-1cn.mm"
include "cdivcncf.mm"
include "mp1i.mm"
include "cncfco.mm"
include "cmo.mm"
include "cif.mm"
include "cn.mm"
include "dirkerval.mm"
include "reseq1d.mm"
include "resmptd.mm"
include "mod0.mm"
include "iffalsed.mm"
include "eqtrd.mm"
include "tgioo2.mm"
include "ctop.mm"
include "cvv.mm"
include "cnfldtop.mm"
include "reex.mm"
include "restabs.mm"
include "mp3an.mm"
include "unicntop.mm"
include "restid.mm"
include "ax-mp.mm"
include "cncfcn.mm"
include "3eltr3d.mm"
include "ctopon.mm"
include "retopon.mm"
include "resttopon.mm"
include "cnfldtopon.mm"
include "cncnp.mm"
include "simprd.mm"
include "mtbid.mm"
include "flltnz.mm"
include "ltmul1dd.mm"
include "divcan1d.mm"
include "syl5eqbr.mm"
include "cle.mm"
include "fllelt.mm"
include "3brtr3d.mm"
include "eliood.mm"
include "fveq2.mm"
include "eleq2d.mm"
include "rspccva.mm"
include "dirkerf.mm"
include "fssresd.mm"
include "ax-resscn.mm"
include "cuni.mm"
include "retop.mm"
include "uniretop.mm"
include "restuni.mm"
include "mp2an.mm"
include "cnprest2.mm"
include "oveq2d.mm"
include "fveq1d.mm"
include "eleqtrd.mm"
include "cnt.mm"
include "iooretop.mm"
include "isopn3.mm"
include "mpbii.mm"
include "eqcomd.mm"
include "cnprest.mm"
include "syl22anc.mm"
include "mpbird.mm"

theorem dirkercncflem4
  let wph: wff ph
  let vy: setvar y
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let vn: setvar n
  let cE: class E
  let cN: class N
  let cY: class Y
  let vx: setvar x
  let vk: setvar k
  assume dirkercncflem4.d: |- D = ( n e. NN |-> ( y e. RR |-> if ( ( y mod ( 2 x. _pi ) ) = 0 , ( ( ( 2 x. n ) + 1 ) / ( 2 x. _pi ) ) , ( ( sin ` ( ( n + ( 1 / 2 ) ) x. y ) ) / ( ( 2 x. _pi ) x. ( sin ` ( y / 2 ) ) ) ) ) ) )
  assume dirkercncflem4.n: |- ( ph -> N e. NN )
  assume dirkercncflem4.y: |- ( ph -> Y e. RR )
  assume dirkercncflem4.ymod0: |- ( ph -> ( Y mod ( 2 x. _pi ) ) =/= 0 )
  assume dirkercncflem4.a: |- A = ( |_ ` ( Y / ( 2 x. _pi ) ) )
  assume dirkercncflem4.b: |- B = ( A + 1 )
  assume dirkercncflem4.c: |- C = ( A x. ( 2 x. _pi ) )
  assume dirkercncflem4.e: |- E = ( B x. ( 2 x. _pi ) )

  disjoint C y
  disjoint D y
  disjoint E y
  disjoint N y
  disjoint Y y
  disjoint n y
  disjoint ph y
  disjoint x y
  disjoint k x
  assert |- ( ph -> ( D ` N ) e. ( ( ( topGen ` ran (,) ) CnP ( topGen ` ran (,) ) ) ` Y ) )

  proof
    wph
    cN
    cD
    cfv
    #
    cY
    cioo
    crn
    ctg
    cfv
    #
    @1
    ccnp
    co
    cfv
    wcel
    #
    @0
    cC
    cE
    cioo
    co
    #
    cres
    #
    cY
    @1
    @3
    crest
    co
    #
    @1
    ccnp
    co
    #
    cfv
    #
    wcel
    #
    wph
    @4
    cY
    @5
    ccnfld
    ctopn
    cfv
    #
    cr
    crest
    co
    #
    ccnp
    co
    #
    cfv
    #
    @7
    wph
    @4
    cY
    @5
    @9
    ccnp
    co
    #
    cfv
    #
    wcel
    #
    @4
    @12
    wcel
    #
    wph
    @4
    vy
    cv
    #
    @13
    cfv
    #
    wcel
    #
    vy
    @3
    wral
    #
    cY
    @3
    wcel
    @15
    wph
    @3
    cc
    @4
    wf
    #
    @20
    wph
    @4
    @5
    @9
    ccn
    co
    #
    wcel
    #
    @21
    @20
    wa
    #
    wph
    vy
    @3
    cN
    c1
    c2
    cdiv
    co
    #
    caddc
    co
    #
    @17
    cmul
    co
    #
    csin
    cfv
    #
    c1
    c2
    cpi
    cmul
    co
    #
    @17
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
    cmul
    co
    #
    cmpt
    #
    @3
    cc
    ccncf
    co
    #
    @4
    @22
    wph
    vy
    @28
    @33
    @3
    wph
    vy
    @27
    csin
    @3
    csin
    cc
    cc
    ccncf
    co
    wcel
    wph
    sincn
    a1i
    #
    wph
    vy
    @26
    @17
    @3
    wph
    vy
    @3
    @26
    cc
    @3
    cc
    wss
    #
    wph
    cC
    cE
    ioosscn
    a1i
    #
    wph
    cN
    @25
    wph
    cN
    dirkercncflem4.n
    nncnd
    #
    wph
    c1
    wph
    1cnd
    #
    halfcld
    #
    addcld
    cc
    cc
    wss
    #
    wph
    cc
    ssid
    a1i
    #
    constcncfg
    wph
    vy
    @3
    cc
    @39
    @44
    idcncfg
    #
    mulcncf
    cncfmpt1f
    wph
    vx
    cc
    cc0
    csn
    #
    cdif
    #
    c1
    vx
    cv
    #
    cdiv
    co
    #
    cmpt
    #
    vy
    @3
    @32
    cmpt
    #
    ccom
    vy
    @3
    @33
    cmpt
    @36
    wph
    vy
    vx
    @3
    @47
    @32
    @49
    @33
    @51
    @50
    wph
    @17
    @3
    wcel
    #
    wa
    #
    @32
    cc
    @46
    @53
    @29
    @31
    @53
    c2
    cpi
    @53
    2cnd
    #
    @53
    cpi
    cpi
    crp
    wcel
    #
    @53
    pirp
    a1i
    #
    rpcnd
    #
    mulcld
    #
    @53
    @30
    @53
    @17
    @53
    @17
    wph
    @3
    cr
    @17
    @3
    cr
    wss
    #
    wph
    cC
    cE
    ioossre
    #
    a1i
    #
    sselda
    #
    recnd
    #
    halfcld
    #
    sincld
    #
    mulcld
    #
    @53
    @32
    @46
    wcel
    #
    @32
    cc0
    wceq
    #
    @53
    @32
    cc0
    @53
    @29
    @31
    @58
    @65
    @53
    c2
    cpi
    @54
    @57
    @53
    c2
    c2
    crp
    wcel
    #
    @53
    2rp
    a1i
    #
    rpne0d
    #
    @53
    cpi
    @56
    rpne0d
    #
    mulne0d
    @53
    @31
    cc0
    @53
    @31
    cc0
    wceq
    #
    @30
    cpi
    cdiv
    co
    #
    cz
    wcel
    #
    @53
    @74
    @17
    @29
    cdiv
    co
    #
    cz
    @53
    @17
    c2
    cpi
    @63
    @54
    @57
    @71
    @72
    divdiv1d
    @53
    cC
    @29
    cdiv
    co
    #
    cz
    wcel
    #
    @77
    @76
    clt
    wbr
    @76
    @77
    c1
    caddc
    co
    #
    clt
    wbr
    @76
    cz
    wcel
    #
    wn
    wph
    @78
    @52
    wph
    @77
    cY
    @29
    cdiv
    co
    #
    cfl
    cfv
    #
    cz
    wph
    @77
    @82
    @29
    cmul
    co
    #
    @29
    cdiv
    co
    @82
    cC
    @83
    @29
    cdiv
    cC
    cA
    @29
    cmul
    co
    #
    @83
    dirkercncflem4.c
    cA
    @82
    @29
    cmul
    dirkercncflem4.a
    oveq1i
    eqtri
    #
    oveq1i
    wph
    @82
    @29
    wph
    @82
    wph
    @82
    wph
    @81
    wph
    cY
    @29
    dirkercncflem4.y
    @29
    cr
    wcel
    wph
    c2
    cpi
    2re
    pire
    remulcli
    a1i
    #
    @29
    cc0
    wne
    wph
    cc0
    @29
    0re
    c2
    cpi
    2re
    pire
    2pos
    pipos
    mulgt0ii
    gtneii
    a1i
    #
    redivcld
    #
    flcld
    #
    zred
    #
    recnd
    #
    wph
    @29
    @86
    recnd
    #
    @87
    divcan4d
    syl5eq
    @89
    eqeltrd
    adantr
    @53
    cC
    @17
    @29
    wph
    cC
    cr
    wcel
    @52
    wph
    cC
    @83
    cr
    @85
    wph
    @82
    @29
    @90
    @86
    remulcld
    syl5eqel
    #
    adantr
    @62
    @53
    c2
    cpi
    @70
    @56
    rpmulcld
    #
    @53
    @17
    cr
    wcel
    #
    cC
    @17
    clt
    wbr
    #
    @17
    cE
    clt
    wbr
    #
    @53
    @52
    @95
    @96
    @97
    w3a
    #
    wph
    @52
    simpr
    @53
    cC
    cxr
    wcel
    #
    cE
    cxr
    wcel
    #
    @52
    @98
    wb
    wph
    @99
    @52
    wph
    cC
    @93
    rexrd
    #
    adantr
    wph
    @100
    @52
    wph
    cE
    wph
    @82
    c1
    caddc
    co
    #
    @29
    cmul
    co
    #
    cE
    cr
    @103
    cE
    wceq
    wph
    @103
    cB
    @29
    cmul
    co
    #
    cE
    @102
    cB
    @29
    cmul
    @102
    cA
    c1
    caddc
    co
    #
    cB
    @82
    cA
    c1
    caddc
    cA
    @82
    dirkercncflem4.a
    eqcomi
    oveq1i
    dirkercncflem4.b
    eqtr4i
    oveq1i
    dirkercncflem4.e
    eqtr4i
    a1i
    #
    wph
    @102
    @29
    wph
    @82
    c1
    @90
    wph
    1red
    readdcld
    #
    @86
    remulcld
    eqeltrrd
    #
    rexrd
    #
    adantr
    cC
    cE
    @17
    elioo2
    syl2anc
    mpbid
    #
    simp2d
    ltdiv1dd
    @53
    @76
    cE
    @29
    cdiv
    co
    #
    @79
    clt
    @53
    @17
    cE
    @29
    @62
    wph
    cE
    cr
    wcel
    @52
    @108
    adantr
    @94
    @53
    @95
    @96
    @97
    @110
    simp3d
    ltdiv1dd
    wph
    @111
    @79
    wceq
    @52
    wph
    @79
    @84
    @29
    cdiv
    co
    #
    c1
    caddc
    co
    @105
    @111
    wph
    @77
    @112
    c1
    caddc
    wph
    cC
    @84
    @29
    cdiv
    cC
    @84
    wceq
    wph
    dirkercncflem4.c
    a1i
    oveq1d
    oveq1d
    wph
    @112
    cA
    c1
    caddc
    wph
    cA
    @29
    wph
    cA
    @82
    cc
    dirkercncflem4.a
    @91
    syl5eqel
    #
    @92
    @87
    divcan4d
    oveq1d
    wph
    @111
    @105
    @29
    cmul
    co
    #
    @29
    cdiv
    co
    @105
    wph
    cE
    @114
    @29
    cdiv
    cE
    @114
    wceq
    wph
    cE
    @104
    @114
    dirkercncflem4.e
    cB
    @105
    @29
    cmul
    dirkercncflem4.b
    oveq1i
    eqtri
    a1i
    oveq1d
    wph
    @105
    @29
    wph
    cA
    c1
    @113
    @41
    addcld
    @92
    @87
    divcan4d
    eqtr2d
    3eqtrrd
    adantr
    breqtrd
    @77
    @76
    btwnnz
    syl3anc
    #
    eqneltrd
    @53
    @30
    cc
    wcel
    @73
    @75
    wb
    @64
    @30
    sineq0
    syl
    mtbird
    neqned
    mulne0d
    #
    neneqd
    @53
    @32
    cr
    wcel
    @67
    @68
    wb
    @53
    @29
    @31
    @53
    c2
    cpi
    c2
    cr
    wcel
    @53
    2re
    a1i
    cpi
    cr
    wcel
    @53
    pire
    a1i
    remulcld
    @53
    @30
    @53
    @17
    @62
    rehalfcld
    resincld
    remulcld
    @32
    cc0
    cr
    elsng
    syl
    mtbird
    eldifd
    #
    wph
    @51
    eqidd
    wph
    @50
    eqidd
    @48
    @32
    c1
    cdiv
    oveq2
    fmptco
    wph
    @3
    @47
    cc
    @51
    @50
    wph
    vy
    @3
    cc
    @3
    @47
    @32
    @51
    @51
    eqid
    wph
    vy
    @29
    @31
    @3
    wph
    vy
    c2
    cpi
    @3
    wph
    vy
    @3
    c2
    cc
    @39
    wph
    2cnd
    @44
    constcncfg
    wph
    vy
    @3
    cpi
    cc
    @39
    wph
    cpi
    @55
    wph
    pirp
    a1i
    #
    rpcnd
    @44
    constcncfg
    mulcncf
    wph
    vy
    @30
    csin
    @3
    @37
    wph
    vy
    @3
    @30
    cmpt
    vy
    @3
    @17
    @25
    cmul
    co
    #
    cmpt
    @36
    wph
    vy
    @3
    @30
    @119
    @53
    @17
    c2
    @63
    @54
    @71
    divrecd
    mpteq2dva
    wph
    vy
    @17
    @25
    @3
    @45
    wph
    vy
    @3
    @25
    cc
    @39
    @42
    @44
    constcncfg
    mulcncf
    eqeltrd
    cncfmpt1f
    mulcncf
    @3
    @3
    wss
    wph
    @3
    ssid
    a1i
    wph
    cc
    @46
    difssd
    @117
    cncfmptssg
    c1
    cc
    wcel
    @50
    @47
    cc
    ccncf
    co
    wcel
    wph
    ax-1cn
    vx
    c1
    @50
    @50
    eqid
    cdivcncf
    mp1i
    cncfco
    eqeltrrd
    mulcncf
    wph
    @4
    vy
    cr
    @17
    @29
    cmo
    co
    cc0
    wceq
    #
    c2
    cN
    cmul
    co
    c1
    caddc
    co
    @29
    cdiv
    co
    #
    @28
    @32
    cdiv
    co
    #
    cif
    #
    cmpt
    #
    @3
    cres
    vy
    @3
    @123
    cmpt
    @35
    wph
    @0
    @124
    @3
    wph
    cN
    cn
    wcel
    #
    @0
    @124
    wceq
    dirkercncflem4.n
    cD
    vn
    cN
    vy
    dirkercncflem4.d
    dirkerval
    syl
    reseq1d
    wph
    vy
    cr
    @3
    @123
    @61
    resmptd
    wph
    vy
    @3
    @123
    @34
    @53
    @123
    @122
    @34
    @53
    @120
    @121
    @122
    @53
    @120
    @80
    @115
    @53
    @95
    @29
    crp
    wcel
    #
    @120
    @80
    wb
    @62
    wph
    @126
    @52
    wph
    c2
    cpi
    @69
    wph
    2rp
    a1i
    @118
    rpmulcld
    #
    adantr
    @17
    @29
    mod0
    syl2anc
    mtbird
    iffalsed
    @53
    @28
    @32
    @53
    @27
    @53
    @26
    @17
    @53
    cN
    @25
    wph
    cN
    cc
    wcel
    @52
    @40
    adantr
    @53
    c1
    @53
    1cnd
    halfcld
    addcld
    @63
    mulcld
    sincld
    @66
    @116
    divrecd
    eqtrd
    mpteq2dva
    3eqtrrd
    wph
    @38
    @43
    @36
    @22
    wceq
    @39
    @44
    @3
    cc
    @9
    @5
    @9
    @9
    eqid
    #
    @5
    @10
    @3
    crest
    co
    #
    @9
    @3
    crest
    co
    #
    @1
    @10
    @3
    crest
    @9
    @128
    tgioo2
    #
    oveq1i
    @9
    ctop
    wcel
    #
    @59
    cr
    cvv
    wcel
    @129
    @130
    wceq
    @9
    @128
    cnfldtop
    #
    @60
    reex
    @3
    cr
    @9
    ctop
    cvv
    restabs
    mp3an
    eqtri
    @9
    cc
    crest
    co
    #
    @9
    @132
    @134
    @9
    wceq
    @133
    @9
    ctop
    cc
    unicntop
    restid
    ax-mp
    eqcomi
    cncfcn
    syl2anc
    3eltr3d
    wph
    @5
    @3
    ctopon
    cfv
    wcel
    #
    @9
    cc
    ctopon
    cfv
    wcel
    #
    @23
    @24
    wb
    wph
    @1
    cr
    ctopon
    cfv
    wcel
    #
    @59
    @135
    @137
    wph
    retopon
    a1i
    @61
    @3
    @1
    cr
    resttopon
    syl2anc
    @136
    wph
    @9
    @128
    cnfldtopon
    a1i
    vy
    @4
    @5
    @9
    @3
    cc
    cncnp
    syl2anc
    mpbid
    simprd
    wph
    cC
    cE
    cY
    @101
    @109
    dirkercncflem4.y
    wph
    cC
    @83
    cY
    clt
    @85
    wph
    @83
    @81
    @29
    cmul
    co
    #
    cY
    clt
    wph
    @82
    @81
    @29
    @90
    @88
    @127
    wph
    @81
    cr
    wcel
    #
    @81
    cz
    wcel
    #
    wn
    @82
    @81
    clt
    wbr
    @88
    wph
    cY
    @29
    cmo
    co
    #
    cc0
    wceq
    #
    @140
    wph
    @141
    cc0
    dirkercncflem4.ymod0
    neneqd
    wph
    cY
    cr
    wcel
    @126
    @142
    @140
    wb
    dirkercncflem4.y
    @127
    cY
    @29
    mod0
    syl2anc
    mtbid
    @81
    flltnz
    syl2anc
    ltmul1dd
    wph
    cY
    @29
    wph
    cY
    dirkercncflem4.y
    recnd
    @92
    @87
    divcan1d
    #
    breqtrd
    syl5eqbr
    wph
    @138
    @103
    cY
    cE
    clt
    wph
    @81
    @102
    @29
    @88
    @107
    @127
    wph
    @82
    @81
    cle
    wbr
    #
    @81
    @102
    clt
    wbr
    #
    wph
    @139
    @144
    @145
    wa
    @88
    @81
    fllelt
    syl
    simprd
    ltmul1dd
    @143
    @106
    3brtr3d
    eliood
    #
    @19
    @15
    vy
    cY
    @3
    @17
    cY
    wceq
    @18
    @14
    @4
    @17
    cY
    @13
    fveq2
    eleq2d
    rspccva
    syl2anc
    wph
    @132
    @3
    cr
    @4
    wf
    cr
    cc
    wss
    #
    @15
    @16
    wb
    @132
    wph
    @133
    a1i
    wph
    cr
    cr
    @3
    @0
    wph
    @125
    cr
    cr
    @0
    wf
    #
    dirkercncflem4.n
    vy
    cD
    vn
    cN
    dirkercncflem4.d
    dirkerf
    syl
    #
    @61
    fssresd
    @147
    wph
    ax-resscn
    a1i
    cr
    cY
    @4
    @5
    @9
    @3
    cc
    @1
    ctop
    wcel
    #
    @59
    @3
    @5
    cuni
    wceq
    retop
    @60
    @3
    @1
    cr
    uniretop
    restuni
    mp2an
    unicntop
    cnprest2
    syl3anc
    mpbid
    wph
    cY
    @11
    @6
    wph
    @10
    @1
    @5
    ccnp
    @10
    @1
    wceq
    wph
    @1
    @10
    @131
    eqcomi
    a1i
    oveq2d
    fveq1d
    eleqtrd
    wph
    @150
    @59
    cY
    @3
    @1
    cnt
    cfv
    cfv
    #
    wcel
    @148
    @2
    @8
    wb
    @150
    wph
    retop
    a1i
    #
    @61
    wph
    cY
    @3
    @151
    @146
    wph
    @151
    @3
    wph
    @150
    @59
    @151
    @3
    wceq
    #
    @152
    @61
    @150
    @59
    wa
    @3
    @1
    wcel
    @153
    cC
    cE
    iooretop
    @3
    @1
    cr
    uniretop
    isopn3
    mpbii
    syl2anc
    eqcomd
    eleqtrd
    @149
    @3
    cY
    @0
    @1
    @1
    cr
    cr
    uniretop
    uniretop
    cnprest
    syl22anc
    mpbird
end
