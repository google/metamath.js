include "cv.mm"
include "cr.mm"
include "wcel.mm"
include "cfv.mm"
include "crn.mm"
include "clt.mm"
include "csup.mm"
include "wceq.mm"
include "cle.mm"
include "wbr.mm"
include "wn.mm"
include "wral.mm"
include "rpnnen1lem3.mm"
include "wss.mm"
include "c0.mm"
include "wne.mm"
include "wrex.mm"
include "wb.mm"
include "cn.mm"
include "cq.mm"
include "wf.mm"
include "cmap.mm"
include "co.mm"
include "rpnnen1lem1.mm"
include "elmap.mm"
include "sylib.mm"
include "frn.mm"
include "qssre.mm"
include "syl6ss.mm"
include "syl.mm"
include "cdm.mm"
include "c1.mm"
include "1nn.mm"
include "ne0ii.mm"
include "fdm.mm"
include "neeq1d.mm"
include "mpbiri.mm"
include "dm0rn0.mm"
include "necon3bii.mm"
include "breq2.mm"
include "ralbidv.mm"
include "rspcev.mm"
include "mpdan.mm"
include "id.mm"
include "suprleub.mm"
include "syl31anc.mm"
include "mpbird.mm"
include "cmin.mm"
include "cdiv.mm"
include "wa.mm"
include "rpnnen1lem4.mm"
include "resubcl.mm"
include "adantr.mm"
include "cc0.mm"
include "posdif.mm"
include "mpancom.mm"
include "biimpa.mm"
include "gt0ne0d.mm"
include "rereccld.mm"
include "arch.mm"
include "ex.mm"
include "w3a.mm"
include "caddc.mm"
include "rpnnen1lem2.mm"
include "zred.mm"
include "3adant3.mm"
include "ltp1d.mm"
include "wi.mm"
include "jca.mm"
include "nnre.mm"
include "nngt0.mm"
include "ltrec1.mm"
include "syl2an.mm"
include "ad2antrr.mm"
include "nnrecre.mm"
include "adantl.mm"
include "simpll.mm"
include "ltaddsub2d.mm"
include "wfn.mm"
include "ffn.mm"
include "fnfvelrn.mm"
include "sylan.mm"
include "sseldd.mm"
include "3jca.mm"
include "suprub.mm"
include "syl2anc.mm"
include "leadd1dd.mm"
include "readdcld.mm"
include "readdcl.mm"
include "simpl.mm"
include "lelttr.mm"
include "expd.mm"
include "syl3anc.mm"
include "mpd.mm"
include "adantlr.mm"
include "sylbird.mm"
include "sylbid.mm"
include "cz.mm"
include "peano2zd.mm"
include "oveq1.mm"
include "breq1d.mm"
include "elrab2.mm"
include "biimpri.mm"
include "crab.mm"
include "ssrab2.mm"
include "eqsstri.mm"
include "zssre.mm"
include "sstri.mm"
include "a1i.mm"
include "cmul.mm"
include "remulcl.mm"
include "ancoms.mm"
include "sylan2.mm"
include "btwnz.mm"
include "simpld.mm"
include "zre.mm"
include "ad2antlr.mm"
include "ltdivmul.mm"
include "rexbidva.mm"
include "rabn0.mm"
include "sylibr.mm"
include "neeq1i.mm"
include "rabeq2i.mm"
include "ltle.mm"
include "impr.mm"
include "sylan2b.mm"
include "ralrimiva.mm"
include "syldan.mm"
include "cc.mm"
include "zcnd.mm"
include "1cnd.mm"
include "nncn.mm"
include "nnne0.mm"
include "divdir.mm"
include "cmpt.mm"
include "cvv.mm"
include "mptex.mm"
include "fvmpt2.mm"
include "mpan2.mm"
include "fveq1d.mm"
include "ovex.mm"
include "eqid.mm"
include "sylan9eq.mm"
include "oveq1d.mm"
include "eqtr4d.mm"
include "lenltd.mm"
include "3imtr3d.mm"
include "syld.mm"
include "exp31.mm"
include "com4l.mm"
include "com14.mm"
include "3imp.mm"
include "mt2d.mm"
include "rexlimdv3a.mm"
include "pm2.01d.mm"
include "eqlelt.mm"
include "mpbir2and.mm"

theorem rpnnen1lem5
  let vx: setvar x
  let cT: class T
  let vk: setvar k
  let vn: setvar n
  let cF: class F
  let vy: setvar y
  assume rpnnen1lem.1: |- T = { n e. ZZ | ( n / k ) < x }
  assume rpnnen1lem.2: |- F = ( x e. RR |-> ( k e. NN |-> ( sup ( T , RR , < ) / k ) ) )
  assume rpnnen1lem.n: |- NN e. _V
  assume rpnnen1lem.q: |- QQ e. _V

  disjoint F k
  disjoint F n
  disjoint F x
  disjoint k n
  disjoint k x
  disjoint n x
  disjoint T n
  disjoint F y
  disjoint k y
  disjoint n y
  disjoint x y
  disjoint T y
  assert |- ( x e. RR -> sup ( ran ( F ` x ) , RR , < ) = x )

  proof
    vx
    cv
    #
    cr
    wcel
    #
    @0
    cF
    cfv
    #
    crn
    #
    cr
    clt
    csup
    #
    @0
    wceq
    #
    @4
    @0
    cle
    wbr
    #
    @4
    @0
    clt
    wbr
    #
    wn
    #
    @1
    @6
    vn
    cv
    #
    @0
    cle
    wbr
    #
    vn
    @3
    wral
    #
    vx
    cT
    vk
    vn
    cF
    rpnnen1lem.1
    rpnnen1lem.2
    rpnnen1lem.n
    rpnnen1lem.q
    rpnnen1lem3
    #
    @1
    @3
    cr
    wss
    #
    @3
    c0
    wne
    #
    @9
    vy
    cv
    #
    cle
    wbr
    #
    vn
    @3
    wral
    #
    vy
    cr
    wrex
    #
    @1
    @6
    @11
    wb
    @1
    cn
    cq
    @2
    wf
    #
    @13
    @1
    @2
    cq
    cn
    cmap
    co
    wcel
    @19
    vx
    cT
    vk
    vn
    cF
    rpnnen1lem.1
    rpnnen1lem.2
    rpnnen1lem.n
    rpnnen1lem.q
    rpnnen1lem1
    cq
    cn
    @2
    rpnnen1lem.q
    rpnnen1lem.n
    elmap
    sylib
    #
    @19
    @3
    cq
    cr
    cn
    cq
    @2
    frn
    qssre
    syl6ss
    syl
    #
    @1
    @19
    @14
    @20
    @19
    @2
    cdm
    #
    c0
    wne
    #
    @14
    @19
    @23
    cn
    c0
    wne
    c1
    cn
    1nn
    ne0ii
    @19
    @22
    cn
    c0
    cn
    cq
    @2
    fdm
    neeq1d
    mpbiri
    @22
    c0
    @3
    c0
    @2
    dm0rn0
    necon3bii
    sylib
    syl
    #
    @1
    @11
    @18
    @12
    @17
    @11
    vy
    @0
    cr
    @15
    @0
    wceq
    @16
    @10
    vn
    @3
    @15
    @0
    @9
    cle
    breq2
    ralbidv
    rspcev
    mpdan
    #
    @1
    id
    vy
    vn
    vn
    @3
    @0
    suprleub
    syl31anc
    mpbird
    @1
    @7
    @1
    @7
    c1
    @0
    @4
    cmin
    co
    #
    cdiv
    co
    #
    vk
    cv
    #
    clt
    wbr
    #
    vk
    cn
    wrex
    #
    @8
    @1
    @7
    @30
    @1
    @7
    wa
    #
    @27
    cr
    wcel
    @30
    @31
    @26
    @1
    @26
    cr
    wcel
    #
    @7
    @1
    @4
    cr
    wcel
    #
    @32
    vx
    cT
    vk
    vn
    cF
    rpnnen1lem.1
    rpnnen1lem.2
    rpnnen1lem.n
    rpnnen1lem.q
    rpnnen1lem4
    #
    @0
    @4
    resubcl
    mpdan
    adantr
    #
    @31
    @26
    @1
    @7
    cc0
    @26
    clt
    wbr
    #
    @33
    @1
    @7
    @36
    wb
    @34
    @4
    @0
    posdif
    mpancom
    biimpa
    #
    gt0ne0d
    rereccld
    @27
    vk
    arch
    syl
    ex
    @1
    @29
    @8
    vk
    cn
    @1
    @28
    cn
    wcel
    #
    @29
    w3a
    #
    @7
    cT
    cr
    clt
    csup
    #
    @40
    c1
    caddc
    co
    #
    clt
    wbr
    #
    @39
    @40
    @1
    @38
    @40
    cr
    wcel
    @29
    @1
    @38
    wa
    #
    @40
    vx
    cT
    vk
    vn
    cF
    rpnnen1lem.1
    rpnnen1lem.2
    rpnnen1lem2
    #
    zred
    #
    3adant3
    ltp1d
    @1
    @38
    @29
    @7
    @42
    wn
    #
    wi
    @7
    @38
    @29
    @1
    @46
    @1
    @7
    @38
    @29
    @46
    @1
    @7
    @38
    @29
    @46
    wi
    @31
    @38
    wa
    #
    @29
    @28
    @2
    cfv
    #
    c1
    @28
    cdiv
    co
    #
    caddc
    co
    #
    @0
    clt
    wbr
    #
    @46
    @47
    @29
    @49
    @26
    clt
    wbr
    #
    @51
    @31
    @32
    @36
    wa
    @28
    cr
    wcel
    #
    cc0
    @28
    clt
    wbr
    #
    wa
    #
    @29
    @52
    wb
    @38
    @31
    @32
    @36
    @35
    @37
    jca
    @38
    @53
    @54
    @28
    nnre
    #
    @28
    nngt0
    jca
    #
    @26
    @28
    ltrec1
    syl2an
    @47
    @52
    @4
    @49
    caddc
    co
    #
    @0
    clt
    wbr
    #
    @51
    @47
    @4
    @49
    @0
    @1
    @33
    @7
    @38
    @34
    ad2antrr
    @38
    @49
    cr
    wcel
    #
    @31
    @28
    nnrecre
    #
    adantl
    @1
    @7
    @38
    simpll
    ltaddsub2d
    @1
    @38
    @59
    @51
    wi
    #
    @7
    @43
    @50
    @58
    cle
    wbr
    #
    @62
    @43
    @48
    @4
    @49
    @43
    @3
    cr
    @48
    @1
    @13
    @38
    @21
    adantr
    @1
    @2
    cn
    wfn
    #
    @38
    @48
    @3
    wcel
    #
    @1
    @19
    @64
    @20
    cn
    cq
    @2
    ffn
    syl
    cn
    @28
    @2
    fnfvelrn
    sylan
    #
    sseldd
    #
    @1
    @33
    @38
    @34
    adantr
    @38
    @60
    @1
    @61
    adantl
    #
    @43
    @13
    @14
    @18
    w3a
    #
    @65
    @48
    @4
    cle
    wbr
    @1
    @69
    @38
    @1
    @13
    @14
    @18
    @21
    @24
    @25
    3jca
    adantr
    @66
    vy
    vn
    @3
    @48
    suprub
    syl2anc
    leadd1dd
    @43
    @50
    cr
    wcel
    #
    @58
    cr
    wcel
    #
    @1
    @63
    @62
    wi
    @43
    @48
    @49
    @67
    @68
    readdcld
    @1
    @33
    @60
    @71
    @38
    @34
    @61
    @4
    @49
    readdcl
    syl2an
    @1
    @38
    simpl
    @70
    @71
    @1
    w3a
    @63
    @59
    @51
    @50
    @58
    @0
    lelttr
    expd
    syl3anc
    mpd
    adantlr
    sylbird
    sylbid
    @1
    @38
    @51
    @46
    wi
    @7
    @43
    @41
    @28
    cdiv
    co
    #
    @0
    clt
    wbr
    #
    @41
    @40
    cle
    wbr
    #
    @51
    @46
    @43
    @73
    @74
    @43
    @73
    @41
    cT
    wcel
    #
    @74
    @43
    @41
    cz
    wcel
    #
    @73
    @75
    @43
    @40
    @44
    peano2zd
    #
    @75
    @76
    @73
    wa
    @9
    @28
    cdiv
    co
    #
    @0
    clt
    wbr
    #
    @73
    vn
    @41
    cz
    cT
    @9
    @41
    wceq
    @78
    @72
    @0
    clt
    @9
    @41
    @28
    cdiv
    oveq1
    breq1d
    rpnnen1lem.1
    elrab2
    biimpri
    sylan
    @43
    cT
    cr
    wss
    #
    cT
    c0
    wne
    #
    @16
    vn
    cT
    wral
    #
    vy
    cr
    wrex
    #
    w3a
    @75
    @74
    @43
    @80
    @81
    @83
    @80
    @43
    cT
    cz
    cr
    cT
    @79
    vn
    cz
    crab
    #
    cz
    rpnnen1lem.1
    @79
    vn
    cz
    ssrab2
    eqsstri
    zssre
    sstri
    a1i
    @43
    @84
    c0
    wne
    #
    @81
    @43
    @79
    vn
    cz
    wrex
    #
    @85
    @43
    @86
    @9
    @28
    @0
    cmul
    co
    #
    clt
    wbr
    #
    vn
    cz
    wrex
    #
    @43
    @87
    cr
    wcel
    #
    @89
    @38
    @1
    @53
    @90
    @56
    @53
    @1
    @90
    @28
    @0
    remulcl
    #
    ancoms
    sylan2
    #
    @90
    @89
    @87
    @9
    clt
    wbr
    vn
    cz
    wrex
    vn
    vn
    @87
    btwnz
    simpld
    syl
    @43
    @79
    @88
    vn
    cz
    @43
    @9
    cz
    wcel
    #
    wa
    #
    @9
    cr
    wcel
    #
    @1
    @55
    @79
    @88
    wb
    @93
    @95
    @43
    @9
    zre
    adantl
    #
    @1
    @38
    @93
    simpll
    #
    @38
    @55
    @1
    @93
    @57
    ad2antlr
    @9
    @0
    @28
    ltdivmul
    syl3anc
    #
    rexbidva
    mpbird
    @79
    vn
    cz
    rabn0
    sylibr
    cT
    @84
    c0
    rpnnen1lem.1
    neeq1i
    sylibr
    @43
    @90
    @9
    @87
    cle
    wbr
    #
    vn
    cT
    wral
    #
    @83
    @92
    @43
    @99
    vn
    cT
    @9
    cT
    wcel
    @43
    @93
    @79
    wa
    @99
    @79
    vn
    cT
    cz
    rpnnen1lem.1
    rabeq2i
    @43
    @93
    @79
    @99
    @94
    @79
    @88
    @99
    @98
    @94
    @95
    @90
    @88
    @99
    wi
    @96
    @94
    @53
    @1
    @90
    @38
    @53
    @1
    @93
    @56
    ad2antlr
    @97
    @91
    syl2anc
    @9
    @87
    ltle
    syl2anc
    sylbid
    impr
    sylan2b
    ralrimiva
    @82
    @100
    vy
    @87
    cr
    @15
    @87
    wceq
    @16
    @99
    vn
    cT
    @15
    @87
    @9
    cle
    breq2
    ralbidv
    rspcev
    syl2anc
    3jca
    vy
    vn
    cT
    @41
    suprub
    sylan
    syldan
    ex
    @43
    @72
    @50
    @0
    clt
    @43
    @72
    @40
    @28
    cdiv
    co
    #
    @49
    caddc
    co
    #
    @50
    @43
    @40
    cc
    wcel
    c1
    cc
    wcel
    @28
    cc
    wcel
    #
    @28
    cc0
    wne
    #
    wa
    #
    @72
    @102
    wceq
    @43
    @40
    @44
    zcnd
    @43
    1cnd
    @38
    @105
    @1
    @38
    @103
    @104
    @28
    nncn
    @28
    nnne0
    jca
    adantl
    @40
    c1
    @28
    divdir
    syl3anc
    @43
    @48
    @101
    @49
    caddc
    @1
    @38
    @48
    @28
    vk
    cn
    @101
    cmpt
    #
    cfv
    #
    @101
    @1
    @28
    @2
    @106
    @1
    @106
    cvv
    wcel
    @2
    @106
    wceq
    vk
    cn
    @101
    rpnnen1lem.n
    mptex
    vx
    cr
    @106
    cvv
    cF
    rpnnen1lem.2
    fvmpt2
    mpan2
    fveq1d
    @38
    @101
    cvv
    wcel
    @107
    @101
    wceq
    @40
    @28
    cdiv
    ovex
    vk
    cn
    @101
    cvv
    @106
    @106
    eqid
    fvmpt2
    mpan2
    sylan9eq
    oveq1d
    eqtr4d
    breq1d
    @43
    @41
    @40
    @43
    @41
    @77
    zred
    @45
    lenltd
    3imtr3d
    adantlr
    syld
    exp31
    com4l
    com14
    3imp
    mt2d
    rexlimdv3a
    syld
    pm2.01d
    @33
    @1
    @5
    @6
    @8
    wa
    wb
    @34
    @4
    @0
    eqlelt
    mpancom
    mpbir2and
end
