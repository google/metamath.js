include "wcel.mm"
include "ccnp.mm"
include "co.mm"
include "cfv.mm"
include "wa.mm"
include "cv.mm"
include "cnmcv.mm"
include "cmul.mm"
include "cle.mm"
include "wbr.mm"
include "wral.mm"
include "cr.mm"
include "wrex.mm"
include "c1.mm"
include "wi.mm"
include "crp.mm"
include "cxmt.mm"
include "cba.mm"
include "cnv.mm"
include "imsxmet.mm"
include "ax-mp.mm"
include "eqid.mm"
include "1rp.mm"
include "metcnpi3.mm"
include "mpanr2.mm"
include "mpanl12.mm"
include "cdiv.mm"
include "rpreccl.mm"
include "rpred.mm"
include "ad2antlr.mm"
include "cnsb.mm"
include "wb.mm"
include "wceq.mm"
include "imsdval.mm"
include "mp3an1.mm"
include "breq1d.mm"
include "wf.mm"
include "lnof.mm"
include "mp3an.mm"
include "ffvelrni.mm"
include "syl2an.mm"
include "w3a.mm"
include "3pm3.2i.mm"
include "lnosub.mm"
include "mpan.mm"
include "fveq2d.mm"
include "eqtr4d.mm"
include "imbi12d.mm"
include "ancoms.mm"
include "adantlr.mm"
include "ralbidva.mm"
include "cn0v.mm"
include "fveq2.mm"
include "oveq2d.mm"
include "breq12d.mm"
include "wne.mm"
include "cns.mm"
include "cpv.mm"
include "a1i.mm"
include "simpll.mm"
include "cc.mm"
include "simpr.mm"
include "nvcl.mm"
include "adantr.mm"
include "cc0.mm"
include "clt.mm"
include "nvgt0.mm"
include "biimpa.mm"
include "elrpd.mm"
include "rpdivcl.mm"
include "rpcnd.mm"
include "simprl.mm"
include "nvscl.mm"
include "syl3anc.mm"
include "nvpncan2.mm"
include "rprege0d.mm"
include "nvsge0.mm"
include "rpcn.mm"
include "ad2antrl.mm"
include "recnd.mm"
include "nvz.mm"
include "necon3bid.mm"
include "biimpar.mm"
include "adantl.mm"
include "divcan1d.mm"
include "3eqtrd.mm"
include "rpre.mm"
include "leidd.mm"
include "eqbrtrd.mm"
include "nvgcl.mm"
include "oveq1.mm"
include "rspcv.mm"
include "syl.mm"
include "mpid.mm"
include "sylancr.mm"
include "1red.mm"
include "lemuldiv2d.mm"
include "lnomul.mm"
include "syl2anc.mm"
include "eqtrd.mm"
include "rpcnne0.mm"
include "recdiv.mm"
include "rpne0.mm"
include "divrec2d.mm"
include "eqtr2d.mm"
include "breq2d.mm"
include "3bitr4d.mm"
include "sylibd.mm"
include "anassrs.mm"
include "imp.mm"
include "an32s.mm"
include "lno0.mm"
include "fveq2i.mm"
include "nvz0.mm"
include "eqtri.mm"
include "0le0.mm"
include "eqbrtri.mm"
include "oveq2i.mm"
include "mul01.mm"
include "syl5eq.mm"
include "syl5breqr.mm"
include "ad3antlr.mm"
include "pm2.61ne.mm"
include "ex.mm"
include "ralrimdva.mm"
include "sylbid.mm"
include "ralbidv.mm"
include "rspcev.mm"
include "rexlimdva.mm"
include "syl5.mm"
include "isblo3i.mm"
include "mpbiran.mm"
include "sylibr.mm"

theorem blocnilem
  let cB: class B
  let cC: class C
  let cD: class D
  let cP: class P
  let cT: class T
  let cU: class U
  let cJ: class J
  let cK: class K
  let cL: class L
  let cW: class W
  let cX: class X
  let vw: setvar w
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  assume blocni.8: |- C = ( IndMet ` U )
  assume blocni.d: |- D = ( IndMet ` W )
  assume blocni.j: |- J = ( MetOpen ` C )
  assume blocni.k: |- K = ( MetOpen ` D )
  assume blocni.4: |- L = ( U LnOp W )
  assume blocni.5: |- B = ( U BLnOp W )
  assume blocni.u: |- U e. NrmCVec
  assume blocni.w: |- W e. NrmCVec
  assume blocni.l: |- T e. L
  assume blocnilem.1: |- X = ( BaseSet ` U )


  assert |- ( ( P e. X /\ T e. ( ( J CnP K ) ` P ) ) -> T e. B )

  proof
    cP
    cX
    wcel
    #
    cT
    cP
    cJ
    cK
    ccnp
    co
    cfv
    wcel
    #
    wa
    vz
    cv
    #
    cT
    cfv
    #
    cW
    cnmcv
    cfv
    #
    cfv
    #
    vx
    cv
    #
    @2
    cU
    cnmcv
    cfv
    #
    cfv
    #
    cmul
    co
    #
    cle
    wbr
    #
    vz
    cX
    wral
    #
    vx
    cr
    wrex
    #
    cT
    cB
    wcel
    #
    @0
    @1
    @12
    @1
    @6
    cP
    cC
    co
    #
    vy
    cv
    #
    cle
    wbr
    #
    @6
    cT
    cfv
    #
    cP
    cT
    cfv
    #
    cD
    co
    #
    c1
    cle
    wbr
    #
    wi
    #
    vx
    cX
    wral
    #
    vy
    crp
    wrex
    #
    @0
    @12
    cC
    cX
    cxmt
    cfv
    wcel
    #
    cD
    cW
    cba
    cfv
    #
    cxmt
    cfv
    wcel
    #
    @1
    @23
    cU
    cnv
    wcel
    #
    @24
    blocni.u
    cC
    cU
    cX
    blocnilem.1
    blocni.8
    imsxmet
    ax-mp
    cW
    cnv
    wcel
    #
    @26
    blocni.w
    cD
    cW
    @25
    @25
    eqid
    #
    blocni.d
    imsxmet
    ax-mp
    @24
    @26
    wa
    @1
    c1
    crp
    wcel
    @23
    1rp
    vy
    vx
    c1
    cC
    cD
    cP
    cT
    cJ
    cK
    cX
    @25
    blocni.j
    blocni.k
    metcnpi3
    mpanr2
    mpanl12
    @0
    @22
    @12
    vy
    crp
    @0
    @15
    crp
    wcel
    #
    wa
    #
    @22
    @12
    @31
    @22
    wa
    c1
    @15
    cdiv
    co
    #
    cr
    wcel
    #
    @5
    @32
    @8
    cmul
    co
    #
    cle
    wbr
    #
    vz
    cX
    wral
    #
    @12
    @30
    @33
    @0
    @22
    @30
    @32
    @15
    rpreccl
    #
    rpred
    ad2antlr
    @31
    @22
    @36
    @31
    @22
    @6
    cP
    cU
    cnsb
    cfv
    #
    co
    #
    @7
    cfv
    #
    @15
    cle
    wbr
    #
    @39
    cT
    cfv
    #
    @4
    cfv
    #
    c1
    cle
    wbr
    #
    wi
    #
    vx
    cX
    wral
    #
    @36
    @31
    @21
    @45
    vx
    cX
    @0
    @6
    cX
    wcel
    #
    @21
    @45
    wb
    #
    @30
    @47
    @0
    @48
    @47
    @0
    wa
    #
    @16
    @41
    @20
    @44
    @49
    @14
    @40
    @15
    cle
    @27
    @47
    @0
    @14
    @40
    wceq
    blocni.u
    @6
    cP
    cC
    cU
    @38
    @7
    cX
    blocnilem.1
    @38
    eqid
    #
    @7
    eqid
    #
    blocni.8
    imsdval
    mp3an1
    breq1d
    @49
    @19
    @43
    c1
    cle
    @49
    @19
    @17
    @18
    cW
    cnsb
    cfv
    #
    co
    #
    @4
    cfv
    #
    @43
    @47
    @17
    @25
    wcel
    #
    @18
    @25
    wcel
    #
    @19
    @54
    wceq
    #
    @0
    cX
    @25
    @6
    cT
    @27
    @28
    cT
    cL
    wcel
    #
    cX
    @25
    cT
    wf
    blocni.u
    blocni.w
    blocni.l
    cT
    cU
    cL
    cW
    cX
    @25
    blocnilem.1
    @29
    blocni.4
    lnof
    mp3an
    #
    ffvelrni
    cX
    @25
    cP
    cT
    @59
    ffvelrni
    @28
    @55
    @56
    @57
    blocni.w
    @17
    @18
    cD
    cW
    @52
    @4
    @25
    @29
    @52
    eqid
    #
    @4
    eqid
    #
    blocni.d
    imsdval
    mp3an1
    syl2an
    @49
    @42
    @53
    @4
    @27
    @28
    @58
    w3a
    #
    @49
    @42
    @53
    wceq
    @27
    @28
    @58
    blocni.u
    blocni.w
    blocni.l
    3pm3.2i
    #
    @6
    cP
    cT
    cU
    cL
    @38
    @52
    cW
    cX
    blocnilem.1
    @50
    @60
    blocni.4
    lnosub
    mpan
    fveq2d
    eqtr4d
    breq1d
    imbi12d
    ancoms
    adantlr
    ralbidva
    @31
    @46
    @35
    vz
    cX
    @31
    @2
    cX
    wcel
    #
    wa
    #
    @46
    @35
    @65
    @46
    wa
    @35
    cU
    cn0v
    cfv
    #
    cT
    cfv
    #
    @4
    cfv
    #
    @32
    @66
    @7
    cfv
    #
    cmul
    co
    #
    cle
    wbr
    #
    @2
    @66
    @2
    @66
    wceq
    #
    @5
    @68
    @34
    @70
    cle
    @72
    @3
    @67
    @4
    @2
    @66
    cT
    fveq2
    fveq2d
    @72
    @8
    @69
    @32
    cmul
    @2
    @66
    @7
    fveq2
    oveq2d
    breq12d
    @65
    @2
    @66
    wne
    #
    @46
    @35
    @65
    @73
    wa
    @46
    @35
    @31
    @64
    @73
    @46
    @35
    wi
    @31
    @64
    @73
    wa
    #
    wa
    #
    @46
    cP
    @15
    @8
    cdiv
    co
    #
    @2
    cU
    cns
    cfv
    #
    co
    #
    cU
    cpv
    cfv
    #
    co
    #
    cP
    @38
    co
    #
    cT
    cfv
    #
    @4
    cfv
    #
    c1
    cle
    wbr
    #
    @35
    @75
    @46
    @81
    @7
    cfv
    #
    @15
    cle
    wbr
    #
    @84
    @75
    @85
    @15
    @15
    cle
    @75
    @85
    @78
    @7
    cfv
    #
    @76
    @8
    cmul
    co
    #
    @15
    @75
    @81
    @78
    @7
    @75
    @27
    @0
    @78
    cX
    wcel
    #
    @81
    @78
    wceq
    @27
    @75
    blocni.u
    a1i
    #
    @0
    @30
    @74
    simpll
    #
    @75
    @27
    @76
    cc
    wcel
    #
    @64
    @89
    @90
    @75
    @76
    @31
    @30
    @8
    crp
    wcel
    #
    @76
    crp
    wcel
    @74
    @0
    @30
    simpr
    #
    @74
    @8
    @64
    @8
    cr
    wcel
    #
    @73
    @27
    @64
    @95
    blocni.u
    @2
    cU
    @7
    cX
    blocnilem.1
    @51
    nvcl
    mpan
    #
    adantr
    @64
    @73
    cc0
    @8
    clt
    wbr
    #
    @27
    @64
    @73
    @97
    wb
    blocni.u
    @2
    cU
    @7
    cX
    @66
    blocnilem.1
    @66
    eqid
    #
    @51
    nvgt0
    mpan
    biimpa
    elrpd
    #
    @15
    @8
    rpdivcl
    syl2an
    #
    rpcnd
    #
    @31
    @64
    @73
    simprl
    #
    @76
    @2
    @77
    cU
    cX
    blocnilem.1
    @77
    eqid
    #
    nvscl
    syl3anc
    #
    cP
    @78
    cU
    @79
    @38
    cX
    blocnilem.1
    @79
    eqid
    #
    @50
    nvpncan2
    syl3anc
    #
    fveq2d
    @75
    @27
    @76
    cr
    wcel
    cc0
    @76
    cle
    wbr
    wa
    #
    @64
    @87
    @88
    wceq
    @90
    @75
    @76
    @100
    rprege0d
    #
    @102
    @76
    @2
    @77
    cU
    @7
    cX
    blocnilem.1
    @103
    @51
    nvsge0
    syl3anc
    @75
    @15
    @8
    @30
    @15
    cc
    wcel
    #
    @0
    @74
    @15
    rpcn
    ad2antlr
    #
    @75
    @8
    @64
    @95
    @31
    @73
    @96
    ad2antrl
    recnd
    #
    @74
    @8
    cc0
    wne
    #
    @31
    @64
    @112
    @73
    @64
    @8
    cc0
    @2
    @66
    @27
    @64
    @8
    cc0
    wceq
    @72
    wb
    blocni.u
    @2
    cU
    @7
    cX
    @66
    blocnilem.1
    @98
    @51
    nvz
    mpan
    necon3bid
    biimpar
    adantl
    divcan1d
    3eqtrd
    @30
    @15
    @15
    cle
    wbr
    @0
    @74
    @30
    @15
    @15
    rpre
    leidd
    ad2antlr
    eqbrtrd
    @75
    @80
    cX
    wcel
    #
    @46
    @86
    @84
    wi
    #
    wi
    @75
    @27
    @0
    @89
    @113
    @90
    @91
    @104
    cP
    @78
    cU
    @79
    cX
    blocnilem.1
    @105
    nvgcl
    syl3anc
    @45
    @114
    vx
    @80
    cX
    @6
    @80
    wceq
    #
    @41
    @86
    @44
    @84
    @115
    @40
    @85
    @15
    cle
    @115
    @39
    @81
    @7
    @6
    @80
    cP
    @38
    oveq1
    #
    fveq2d
    breq1d
    @115
    @43
    @83
    c1
    cle
    @115
    @42
    @82
    @4
    @115
    @39
    @81
    cT
    @116
    fveq2d
    fveq2d
    breq1d
    imbi12d
    rspcv
    syl
    mpid
    @75
    @76
    @5
    cmul
    co
    #
    c1
    cle
    wbr
    @5
    c1
    @76
    cdiv
    co
    #
    cle
    wbr
    @84
    @35
    @75
    @5
    c1
    @76
    @64
    @5
    cr
    wcel
    #
    @31
    @73
    @64
    @28
    @3
    @25
    wcel
    #
    @119
    blocni.w
    cX
    @25
    @2
    cT
    @59
    ffvelrni
    #
    @3
    cW
    @4
    @25
    @29
    @61
    nvcl
    sylancr
    ad2antrl
    @75
    1red
    @100
    lemuldiv2d
    @75
    @83
    @117
    c1
    cle
    @75
    @83
    @76
    @3
    cW
    cns
    cfv
    #
    co
    #
    @4
    cfv
    #
    @117
    @75
    @82
    @123
    @4
    @75
    @82
    @78
    cT
    cfv
    #
    @123
    @75
    @81
    @78
    cT
    @106
    fveq2d
    @75
    @92
    @64
    @125
    @123
    wceq
    #
    @101
    @102
    @62
    @92
    @64
    wa
    @126
    @63
    @76
    @2
    @77
    @122
    cT
    cU
    cL
    cW
    cX
    blocnilem.1
    @103
    @122
    eqid
    #
    blocni.4
    lnomul
    mpan
    syl2anc
    eqtrd
    fveq2d
    @75
    @28
    @107
    @120
    @124
    @117
    wceq
    @28
    @75
    blocni.w
    a1i
    @108
    @64
    @120
    @31
    @73
    @121
    ad2antrl
    @76
    @3
    @122
    cW
    @4
    @25
    @29
    @127
    @61
    nvsge0
    syl3anc
    eqtrd
    breq1d
    @75
    @34
    @118
    @5
    cle
    @75
    @118
    @8
    @15
    cdiv
    co
    #
    @34
    @31
    @30
    @93
    @118
    @128
    wceq
    #
    @74
    @94
    @99
    @30
    @109
    @15
    cc0
    wne
    #
    wa
    @8
    cc
    wcel
    @112
    wa
    @129
    @93
    @15
    rpcnne0
    @8
    rpcnne0
    @15
    @8
    recdiv
    syl2an
    syl2an
    @75
    @8
    @15
    @111
    @110
    @30
    @130
    @0
    @74
    @15
    rpne0
    ad2antlr
    divrec2d
    eqtr2d
    breq2d
    3bitr4d
    sylibd
    anassrs
    imp
    an32s
    @30
    @71
    @0
    @64
    @46
    @30
    @68
    cc0
    @70
    cle
    @68
    cc0
    cc0
    cle
    @68
    cW
    cn0v
    cfv
    #
    @4
    cfv
    #
    cc0
    @67
    @131
    @4
    @27
    @28
    @58
    @67
    @131
    wceq
    blocni.u
    blocni.w
    blocni.l
    @66
    cT
    cU
    cL
    cW
    cX
    @25
    @131
    blocnilem.1
    @29
    @98
    @131
    eqid
    #
    blocni.4
    lno0
    mp3an
    fveq2i
    @28
    @132
    cc0
    wceq
    blocni.w
    cW
    @4
    @131
    @133
    @61
    nvz0
    ax-mp
    eqtri
    0le0
    eqbrtri
    @30
    @32
    cc
    wcel
    #
    @70
    cc0
    wceq
    @30
    @32
    @37
    rpcnd
    @134
    @70
    @32
    cc0
    cmul
    co
    cc0
    @69
    cc0
    @32
    cmul
    @27
    @69
    cc0
    wceq
    blocni.u
    cU
    @7
    @66
    @98
    @51
    nvz0
    ax-mp
    oveq2i
    @32
    mul01
    syl5eq
    syl
    syl5breqr
    ad3antlr
    pm2.61ne
    ex
    ralrimdva
    sylbid
    imp
    @11
    @36
    vx
    @32
    cr
    @6
    @32
    wceq
    #
    @10
    @35
    vz
    cX
    @135
    @9
    @34
    @5
    cle
    @6
    @32
    @8
    cmul
    oveq1
    breq2d
    ralbidv
    rspcev
    syl2anc
    ex
    rexlimdva
    syl5
    imp
    @13
    @58
    @12
    blocni.l
    vx
    vz
    cB
    cT
    cU
    cL
    @7
    @4
    cW
    cX
    blocnilem.1
    @51
    @61
    blocni.4
    blocni.5
    blocni.u
    blocni.w
    isblo3i
    mpbiran
    sylibr
end
