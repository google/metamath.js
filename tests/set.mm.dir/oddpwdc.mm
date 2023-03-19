include "cn0.mm"
include "cxp.mm"
include "cn.mm"
include "wf1o.mm"
include "wtru.mm"
include "c2.mm"
include "cv.mm"
include "cexp.mm"
include "co.mm"
include "cmul.mm"
include "cdvds.mm"
include "wbr.mm"
include "crab.mm"
include "clt.mm"
include "csup.mm"
include "cdiv.mm"
include "wcel.mm"
include "wa.mm"
include "2nn.mm"
include "a1i.mm"
include "simpl.mm"
include "nnexpcld.mm"
include "wn.mm"
include "ssrab2.mm"
include "eqsstri.mm"
include "simpr.mm"
include "sseldi.mm"
include "nnmulcld.mm"
include "ancoms.mm"
include "adantl.mm"
include "id.mm"
include "wor.mm"
include "cr.mm"
include "wss.mm"
include "nn0ssre.mm"
include "ltso.mm"
include "soss.mm"
include "mp2.mm"
include "cc0.mm"
include "cz.mm"
include "cle.mm"
include "wral.mm"
include "wrex.mm"
include "wi.mm"
include "0zd.mm"
include "nnz.mm"
include "weq.mm"
include "oveq2.mm"
include "breq1d.mm"
include "elrab.mm"
include "simprl.mm"
include "nn0red.mm"
include "nnred.mm"
include "2re.mm"
include "leidi.mm"
include "nexple.mm"
include "mp3an23.mm"
include "ad2antrl.mm"
include "nnzd.mm"
include "simprr.mm"
include "dvdsle.mm"
include "imp.mm"
include "syl21anc.mm"
include "letrd.mm"
include "sylan2b.mm"
include "ralrimiva.mm"
include "breq2.mm"
include "ralbidv.mm"
include "rspcev.mm"
include "syl2anc.mm"
include "nn0uz.mm"
include "uzsupss.mm"
include "syl3anc.mm"
include "supcl.mm"
include "cfn.mm"
include "c0.mm"
include "wne.mm"
include "cfz.mm"
include "fzfi.mm"
include "adantr.mm"
include "nn0zd.mm"
include "nn0ge0d.mm"
include "elfz4.mm"
include "syl32anc.mm"
include "ex.mm"
include "ssrdv.mm"
include "ssfi.mm"
include "sylancr.mm"
include "0nn0.mm"
include "c1.mm"
include "cc.mm"
include "wceq.mm"
include "2cn.mm"
include "exp0.mm"
include "ax-mp.mm"
include "1dvds.mm"
include "syl.mm"
include "syl5eqbr.mm"
include "sylanbrc.mm"
include "ne0i.mm"
include "fisupcl.mm"
include "syl13anc.mm"
include "cbvrabv.mm"
include "syl6eleq.mm"
include "sylib.mm"
include "simprd.mm"
include "nndivdvds.mm"
include "biimpa.mm"
include "caddc.mm"
include "1nn0.mm"
include "nn0addcld.mm"
include "ltp1d.mm"
include "supub.mm"
include "mt2d.mm"
include "eleq2i.mm"
include "sylnib.mm"
include "imnan.mm"
include "sylibr.mm"
include "mpd.mm"
include "expp1.mm"
include "mtbid.mm"
include "nncn.mm"
include "nncnd.mm"
include "nnne0d.mm"
include "divcan2d.mm"
include "eqcomd.mm"
include "breq2d.mm"
include "wb.mm"
include "dvdscmulr.mm"
include "syl112anc.mm"
include "bitrd.mm"
include "notbid.mm"
include "elrab2.mm"
include "jca.mm"
include "simplr.mm"
include "sseli.mm"
include "ad2antrr.mm"
include "eqeltrd.mm"
include "simplll.mm"
include "simprbi.mm"
include "cmin.mm"
include "2z.mm"
include "znnsub.mm"
include "iddvdsexp.mm"
include "nnnn0d.mm"
include "zexpcl.mm"
include "dvdsmultr2.mm"
include "2cnd.mm"
include "expcld.mm"
include "2ne0.mm"
include "expne0d.mm"
include "divcld.mm"
include "mulcld.mm"
include "nn0cnd.mm"
include "pncan3d.mm"
include "oveq2d.mm"
include "expaddd.mm"
include "eqtr3d.mm"
include "oveq1d.mm"
include "3eqtr3d.mm"
include "mulassd.mm"
include "eqtrd.mm"
include "mulcanad.mm"
include "mulcomd.mm"
include "eqtr4d.mm"
include "breqtrrd.mm"
include "nsyl3.mm"
include "pm2.65da.mm"
include "eqtr2d.mm"
include "dvds0lem.mm"
include "syl31anc.mm"
include "lttri3d.mm"
include "mpbir2and.mm"
include "nnexpcl.mm"
include "mpan.mm"
include "ad3antlr.mm"
include "divmul2.mm"
include "mpbird.mm"
include "jcai.mm"
include "ancomd.mm"
include "oveq12d.mm"
include "jca31.mm"
include "impbii.mm"
include "f1od2.mm"
include "trud.mm"

theorem oddpwdc
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cF: class F
  let cJ: class J
  let va: setvar a
  let vk: setvar k
  let vl: setvar l
  let vm: setvar m
  let vn: setvar n
  let vo: setvar o
  assume oddpwdc.j: |- J = { z e. NN | -. 2 || z }
  assume oddpwdc.f: |- F = ( x e. J , y e. NN0 |-> ( ( 2 ^ y ) x. x ) )

  disjoint x y
  disjoint x z
  disjoint y z
  disjoint J x
  disjoint J y
  disjoint a k
  disjoint a l
  disjoint a m
  disjoint a n
  disjoint a o
  disjoint a x
  disjoint a y
  disjoint a z
  disjoint k l
  disjoint k m
  disjoint k n
  disjoint k o
  disjoint k x
  disjoint k y
  disjoint k z
  disjoint l m
  disjoint l n
  disjoint l o
  disjoint l x
  disjoint l y
  disjoint l z
  disjoint m n
  disjoint m o
  disjoint m x
  disjoint m y
  disjoint m z
  disjoint n o
  disjoint n x
  disjoint n y
  disjoint n z
  disjoint o x
  disjoint o y
  disjoint o z
  disjoint F a
  disjoint J a
  assert |- F : ( J X. NN0 ) -1-1-onto-> NN

  proof
    cJ
    cn0
    cxp
    cn
    cF
    wf1o
    wtru
    vx
    vy
    va
    cJ
    cn0
    c2
    vy
    cv
    #
    cexp
    co
    #
    vx
    cv
    #
    cmul
    co
    #
    cn
    cF
    va
    cv
    #
    c2
    c2
    vk
    cv
    #
    cexp
    co
    #
    @4
    cdvds
    wbr
    #
    vk
    cn0
    crab
    #
    cn0
    clt
    csup
    #
    cexp
    co
    #
    cdiv
    co
    #
    @9
    cn
    cJ
    cn0
    oddpwdc.f
    @2
    cJ
    wcel
    #
    @0
    cn0
    wcel
    #
    wa
    #
    @3
    cn
    wcel
    #
    wtru
    @13
    @12
    @15
    @13
    @12
    wa
    #
    @1
    @2
    @16
    c2
    @0
    c2
    cn
    wcel
    #
    @16
    2nn
    a1i
    @13
    @12
    simpl
    nnexpcld
    @16
    cJ
    cn
    @2
    cJ
    c2
    vz
    cv
    #
    cdvds
    wbr
    #
    wn
    #
    vz
    cn
    crab
    cn
    oddpwdc.j
    @20
    vz
    cn
    ssrab2
    eqsstri
    #
    @13
    @12
    simpr
    sseldi
    nnmulcld
    ancoms
    adantl
    @4
    cn
    wcel
    #
    @11
    cJ
    wcel
    #
    @9
    cn0
    wcel
    #
    wa
    wtru
    @22
    @23
    @24
    @22
    @11
    cn
    wcel
    #
    c2
    @11
    cdvds
    wbr
    #
    wn
    #
    @23
    @22
    @22
    @10
    cn
    wcel
    #
    @10
    @4
    cdvds
    wbr
    #
    @25
    @22
    id
    @22
    c2
    @9
    @17
    @22
    2nn
    a1i
    #
    @22
    vm
    vn
    vo
    cn0
    @8
    clt
    cn0
    clt
    wor
    #
    @22
    cn0
    cr
    wss
    cr
    clt
    wor
    @31
    nn0ssre
    ltso
    cn0
    cr
    clt
    soss
    mp2
    #
    a1i
    #
    @22
    cc0
    cz
    wcel
    #
    @8
    cn0
    wss
    #
    vn
    cv
    #
    vm
    cv
    #
    cle
    wbr
    #
    vn
    @8
    wral
    #
    vm
    cz
    wrex
    #
    @37
    @36
    clt
    wbr
    wn
    vn
    @8
    wral
    @36
    @37
    clt
    wbr
    @36
    vo
    cv
    clt
    wbr
    vo
    @8
    wrex
    wi
    vn
    cn0
    wral
    wa
    vm
    cn0
    wrex
    #
    @22
    0zd
    @35
    @22
    @7
    vk
    cn0
    ssrab2
    a1i
    #
    @22
    @4
    cz
    wcel
    #
    @36
    @4
    cle
    wbr
    #
    vn
    @8
    wral
    #
    @40
    @4
    nnz
    #
    @22
    @44
    vn
    @8
    @36
    @8
    wcel
    #
    @22
    @36
    cn0
    wcel
    #
    c2
    @36
    cexp
    co
    #
    @4
    cdvds
    wbr
    #
    wa
    #
    @44
    @7
    @50
    vk
    @36
    cn0
    vk
    vn
    weq
    @6
    @49
    @4
    cdvds
    @5
    @36
    c2
    cexp
    oveq2
    breq1d
    elrab
    #
    @22
    @51
    wa
    #
    @36
    @49
    @4
    @53
    @36
    @22
    @48
    @50
    simprl
    #
    nn0red
    @53
    @49
    @53
    c2
    @36
    @17
    @53
    2nn
    a1i
    @54
    nnexpcld
    #
    nnred
    @53
    @4
    @22
    @51
    simpl
    #
    nnred
    @48
    @36
    @49
    cle
    wbr
    #
    @22
    @50
    @48
    c2
    cr
    wcel
    c2
    c2
    cle
    wbr
    @57
    2re
    c2
    2re
    leidi
    @36
    c2
    nexple
    mp3an23
    ad2antrl
    @53
    @49
    cz
    wcel
    #
    @22
    @50
    @49
    @4
    cle
    wbr
    #
    @53
    @49
    @55
    nnzd
    @56
    @22
    @48
    @50
    simprr
    @58
    @22
    wa
    @50
    @59
    @49
    @4
    dvdsle
    imp
    syl21anc
    letrd
    sylan2b
    #
    ralrimiva
    @39
    @45
    vm
    @4
    cz
    vm
    va
    weq
    @38
    @44
    vn
    @8
    @37
    @4
    @36
    cle
    breq2
    ralbidv
    rspcev
    syl2anc
    vm
    vn
    vo
    @8
    cc0
    cn0
    nn0uz
    uzsupss
    syl3anc
    #
    supcl
    #
    nnexpcld
    #
    @22
    @24
    @29
    @22
    @9
    c2
    vl
    cv
    #
    cexp
    co
    #
    @4
    cdvds
    wbr
    #
    vl
    cn0
    crab
    #
    wcel
    @24
    @29
    wa
    @22
    @9
    @8
    @67
    @22
    @31
    @8
    cfn
    wcel
    #
    @8
    c0
    wne
    #
    @35
    @9
    @8
    wcel
    @33
    @22
    cc0
    @4
    cfz
    co
    #
    cfn
    wcel
    @8
    @70
    wss
    @68
    cc0
    @4
    fzfi
    @22
    vn
    @8
    @70
    @22
    @47
    @36
    @70
    wcel
    #
    @22
    @47
    wa
    #
    @34
    @43
    @36
    cz
    wcel
    cc0
    @36
    cle
    wbr
    @44
    @71
    @72
    0zd
    @22
    @43
    @47
    @46
    adantr
    @72
    @36
    @47
    @22
    @51
    @48
    @52
    @54
    sylan2b
    #
    nn0zd
    @72
    @36
    @73
    nn0ge0d
    @60
    @36
    cc0
    @4
    elfz4
    syl32anc
    ex
    ssrdv
    @70
    @8
    ssfi
    sylancr
    @22
    cc0
    @8
    wcel
    #
    @69
    @22
    cc0
    cn0
    wcel
    #
    c2
    cc0
    cexp
    co
    #
    @4
    cdvds
    wbr
    #
    @74
    @75
    @22
    0nn0
    a1i
    @22
    @76
    c1
    @4
    cdvds
    c2
    cc
    wcel
    #
    @76
    c1
    wceq
    2cn
    c2
    exp0
    ax-mp
    @22
    @43
    c1
    @4
    cdvds
    wbr
    @46
    @4
    1dvds
    syl
    syl5eqbr
    @7
    @77
    vk
    cc0
    cn0
    @5
    cc0
    wceq
    @6
    @76
    @4
    cdvds
    @5
    cc0
    c2
    cexp
    oveq2
    breq1d
    elrab
    sylanbrc
    @8
    cc0
    ne0i
    syl
    @42
    cn0
    @8
    clt
    fisupcl
    syl13anc
    @7
    @66
    vk
    vl
    cn0
    vk
    vl
    weq
    @6
    @65
    @4
    cdvds
    @5
    @64
    c2
    cexp
    oveq2
    breq1d
    cbvrabv
    #
    syl6eleq
    @66
    @29
    vl
    @9
    cn0
    @64
    @9
    wceq
    @65
    @10
    @4
    cdvds
    @64
    @9
    c2
    cexp
    oveq2
    breq1d
    elrab
    sylib
    simprd
    @22
    @28
    wa
    @29
    @25
    @4
    @10
    nndivdvds
    biimpa
    syl21anc
    #
    @22
    @10
    c2
    cmul
    co
    #
    @4
    cdvds
    wbr
    #
    @26
    @22
    c2
    @9
    c1
    caddc
    co
    #
    cexp
    co
    #
    @4
    cdvds
    wbr
    #
    @82
    @22
    @83
    cn0
    wcel
    #
    @85
    wn
    #
    @22
    @9
    c1
    @62
    c1
    cn0
    wcel
    @22
    1nn0
    a1i
    nn0addcld
    @22
    @86
    @85
    wa
    #
    wn
    @86
    @87
    wi
    @22
    @83
    @67
    wcel
    #
    @88
    @22
    @83
    @8
    wcel
    #
    @89
    @22
    @90
    @9
    @83
    clt
    wbr
    @22
    @9
    @22
    @9
    @62
    nn0red
    #
    ltp1d
    @22
    vm
    vn
    vo
    cn0
    @8
    @83
    clt
    @33
    @61
    supub
    mt2d
    @8
    @67
    @83
    @79
    eleq2i
    sylnib
    @66
    @85
    vl
    @83
    cn0
    @64
    @83
    wceq
    @65
    @84
    @4
    cdvds
    @64
    @83
    c2
    cexp
    oveq2
    breq1d
    elrab
    sylnib
    @86
    @85
    imnan
    sylibr
    mpd
    @22
    @84
    @81
    @4
    cdvds
    @22
    @78
    @24
    @84
    @81
    wceq
    2cn
    @62
    c2
    @9
    expp1
    sylancr
    breq1d
    mtbid
    @22
    @82
    @81
    @10
    @11
    cmul
    co
    #
    cdvds
    wbr
    #
    @26
    @22
    @4
    @92
    @81
    cdvds
    @22
    @92
    @4
    @22
    @4
    @10
    @4
    nncn
    @22
    @10
    @63
    nncnd
    #
    @22
    @10
    @63
    nnne0d
    #
    divcan2d
    eqcomd
    #
    breq2d
    @22
    c2
    cz
    wcel
    #
    @11
    cz
    wcel
    #
    @10
    cz
    wcel
    @10
    cc0
    wne
    @93
    @26
    wb
    @22
    c2
    @30
    nnzd
    @22
    @11
    @80
    nnzd
    #
    @22
    @10
    @63
    nnzd
    @95
    @10
    c2
    @11
    dvdscmulr
    syl112anc
    bitrd
    mtbid
    @20
    @27
    vz
    @11
    cn
    cJ
    @18
    @11
    wceq
    @19
    @26
    @18
    @11
    c2
    cdvds
    breq2
    notbid
    oddpwdc.j
    elrab2
    sylanbrc
    #
    @62
    jca
    adantl
    @14
    @4
    @3
    wceq
    #
    wa
    #
    @22
    @2
    @11
    wceq
    #
    @0
    @9
    wceq
    #
    wa
    #
    wa
    #
    wb
    wtru
    @102
    @106
    @102
    @22
    @105
    @102
    @4
    @3
    cn
    @14
    @101
    simpr
    #
    @102
    @1
    @2
    @102
    c2
    @0
    @17
    @102
    2nn
    a1i
    @12
    @13
    @101
    simplr
    #
    nnexpcld
    #
    @12
    @2
    cn
    wcel
    #
    @13
    @101
    cJ
    cn
    @2
    @21
    sseli
    ad2antrr
    #
    nnmulcld
    eqeltrd
    #
    @102
    @104
    @103
    @102
    @104
    @103
    @102
    @104
    @0
    @9
    clt
    wbr
    #
    wn
    @9
    @0
    clt
    wbr
    wn
    #
    @102
    @113
    @12
    @12
    @13
    @101
    @113
    simplll
    @12
    c2
    @2
    cdvds
    wbr
    #
    @102
    @113
    wa
    #
    @12
    @110
    @115
    wn
    #
    @20
    @117
    vz
    @2
    cn
    cJ
    vz
    vx
    weq
    @19
    @115
    @18
    @2
    c2
    cdvds
    breq2
    notbid
    oddpwdc.j
    elrab2
    simprbi
    @116
    c2
    @11
    c2
    @9
    @0
    cmin
    co
    #
    cexp
    co
    #
    cmul
    co
    #
    @2
    cdvds
    @116
    c2
    @119
    cdvds
    wbr
    #
    c2
    @120
    cdvds
    wbr
    #
    @116
    @97
    @118
    cn
    wcel
    #
    @121
    2z
    @116
    @0
    cz
    wcel
    #
    @9
    cz
    wcel
    #
    @113
    @123
    @116
    @0
    @102
    @13
    @113
    @108
    adantr
    #
    nn0zd
    #
    @116
    @9
    @116
    vm
    vn
    vo
    cn0
    @8
    clt
    @31
    @116
    @32
    a1i
    @102
    @41
    @113
    @102
    @22
    @41
    @112
    @61
    syl
    #
    adantr
    supcl
    #
    nn0zd
    #
    @102
    @113
    simpr
    @124
    @125
    wa
    @113
    @123
    @0
    @9
    znnsub
    biimpa
    syl21anc
    #
    c2
    @118
    iddvdsexp
    sylancr
    @116
    @97
    @98
    @119
    cz
    wcel
    #
    @121
    @122
    wi
    @97
    @116
    2z
    a1i
    @102
    @98
    @113
    @102
    @22
    @98
    @112
    @99
    syl
    adantr
    @116
    @97
    @118
    cn0
    wcel
    @132
    2z
    @116
    @118
    @131
    nnnn0d
    #
    c2
    @118
    zexpcl
    sylancr
    c2
    @11
    @119
    dvdsmultr2
    syl3anc
    mpd
    @116
    @2
    @119
    @11
    cmul
    co
    #
    @120
    @116
    @2
    @134
    @1
    @116
    @2
    @102
    @110
    @113
    @111
    adantr
    nncnd
    @116
    @119
    @11
    @116
    c2
    @118
    @116
    2cnd
    #
    @133
    expcld
    #
    @116
    @4
    @10
    @116
    @4
    @102
    @22
    @113
    @112
    adantr
    #
    nncnd
    @116
    @22
    @10
    cc
    wcel
    @137
    @94
    syl
    @116
    c2
    @9
    @135
    c2
    cc0
    wne
    @116
    2ne0
    a1i
    #
    @130
    expne0d
    divcld
    #
    mulcld
    @116
    c2
    @0
    @135
    @126
    expcld
    #
    @116
    c2
    @0
    @135
    @138
    @127
    expne0d
    @116
    @3
    @1
    @119
    cmul
    co
    #
    @11
    cmul
    co
    #
    @1
    @134
    cmul
    co
    @116
    @4
    @92
    @3
    @142
    @116
    @22
    @4
    @92
    wceq
    #
    @137
    @96
    syl
    @14
    @101
    @113
    simplr
    @116
    @10
    @141
    @11
    cmul
    @116
    c2
    @0
    @118
    caddc
    co
    #
    cexp
    co
    @10
    @141
    @116
    @144
    @9
    c2
    cexp
    @116
    @0
    @9
    @116
    @0
    @126
    nn0cnd
    @116
    @9
    @129
    nn0cnd
    pncan3d
    oveq2d
    @116
    c2
    @0
    @118
    @135
    @133
    @126
    expaddd
    eqtr3d
    oveq1d
    3eqtr3d
    @116
    @1
    @119
    @11
    @140
    @136
    @139
    mulassd
    eqtrd
    mulcanad
    @116
    @11
    @119
    @139
    @136
    mulcomd
    eqtr4d
    breqtrrd
    nsyl3
    pm2.65da
    @102
    @0
    @8
    wcel
    #
    @114
    @102
    @13
    @1
    @4
    cdvds
    wbr
    #
    @145
    @108
    @102
    @2
    cz
    wcel
    @1
    cz
    wcel
    @43
    @2
    @1
    cmul
    co
    #
    @4
    wceq
    @146
    @102
    @2
    @111
    nnzd
    @102
    @1
    @109
    nnzd
    @102
    @4
    @112
    nnzd
    @102
    @4
    @3
    @147
    @107
    @102
    @1
    @2
    @102
    @1
    @109
    nncnd
    @102
    @2
    @111
    nncnd
    mulcomd
    eqtr2d
    @2
    @1
    @4
    dvds0lem
    syl31anc
    @7
    @146
    vk
    @0
    cn0
    vk
    vy
    weq
    @6
    @1
    @4
    cdvds
    @5
    @0
    c2
    cexp
    oveq2
    breq1d
    elrab
    sylanbrc
    @102
    vm
    vn
    vo
    cn0
    @8
    @0
    clt
    @31
    @102
    @32
    a1i
    @128
    supub
    mpd
    @102
    @0
    @9
    @102
    @0
    @108
    nn0red
    @102
    @22
    @9
    cr
    wcel
    @112
    @91
    syl
    lttri3d
    mpbir2and
    @102
    @104
    @103
    @102
    @104
    wa
    #
    @4
    @1
    cdiv
    co
    #
    @2
    @11
    @148
    @149
    @2
    wceq
    #
    @101
    @14
    @101
    @104
    simplr
    @148
    @4
    cc
    wcel
    @2
    cc
    wcel
    @1
    cc
    wcel
    #
    @1
    cc0
    wne
    #
    wa
    #
    @150
    @101
    wb
    @148
    @4
    @102
    @22
    @104
    @112
    adantr
    nncnd
    @148
    @2
    @102
    @110
    @104
    @111
    adantr
    nncnd
    @13
    @153
    @12
    @101
    @104
    @13
    @151
    @152
    @13
    @1
    @17
    @13
    @1
    cn
    wcel
    2nn
    c2
    @0
    nnexpcl
    mpan
    #
    nncnd
    @13
    @1
    @154
    nnne0d
    jca
    ad3antlr
    @4
    @2
    @1
    divmul2
    syl3anc
    mpbird
    @148
    @1
    @10
    @4
    cdiv
    @148
    @0
    @9
    c2
    cexp
    @102
    @104
    simpr
    oveq2d
    oveq2d
    eqtr3d
    ex
    jcai
    ancomd
    jca
    @106
    @12
    @13
    @101
    @106
    @2
    @11
    cJ
    @22
    @103
    @104
    simprl
    #
    @22
    @23
    @105
    @100
    adantr
    eqeltrd
    @106
    @0
    @9
    cn0
    @22
    @103
    @104
    simprr
    #
    @22
    @24
    @105
    @62
    adantr
    eqeltrd
    @106
    @4
    @92
    @3
    @22
    @143
    @105
    @96
    adantr
    @106
    @1
    @10
    @2
    @11
    cmul
    @106
    @0
    @9
    c2
    cexp
    @156
    oveq2d
    @155
    oveq12d
    eqtr4d
    jca31
    impbii
    a1i
    f1od2
    trud
end
