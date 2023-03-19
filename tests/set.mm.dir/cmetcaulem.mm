include "cv.mm"
include "cn.mm"
include "cuz.mm"
include "cima.mm"
include "cfg.mm"
include "co.mm"
include "cflf.mm"
include "cfv.mm"
include "wcel.mm"
include "wex.mm"
include "clm.mm"
include "cdm.mm"
include "c0.mm"
include "wne.mm"
include "cfm.mm"
include "cflim.mm"
include "ctopon.mm"
include "cfil.mm"
include "wf.mm"
include "wceq.mm"
include "cxmt.mm"
include "cme.mm"
include "cms.mm"
include "cmetmet.mm"
include "syl.mm"
include "metxmet.mm"
include "mopntopon.mm"
include "cfbas.mm"
include "c1.mm"
include "cz.mm"
include "1z.mm"
include "nnuz.mm"
include "uzfbas.mm"
include "mp1i.mm"
include "fgcl.mm"
include "cif.mm"
include "wa.mm"
include "cc.mm"
include "cvv.mm"
include "cpm.mm"
include "elfvdm.mm"
include "cnex.mm"
include "a1i.mm"
include "cca.mm"
include "caufpm.mm"
include "syl2anc.mm"
include "wss.mm"
include "elpm2g.mm"
include "simprbda.mm"
include "syl21anc.mm"
include "adantr.mm"
include "ffvelrnda.mm"
include "wn.mm"
include "ad2antrr.mm"
include "ifclda.mm"
include "fmptd.mm"
include "flfval.mm"
include "syl3anc.mm"
include "eqid.mm"
include "fmfg.mm"
include "oveq2d.mm"
include "eqtr4d.mm"
include "ccfil.mm"
include "wral.mm"
include "wrex.mm"
include "crp.mm"
include "1rp.mm"
include "clt.mm"
include "wbr.mm"
include "w3a.mm"
include "1zzd.mm"
include "iscau3.mm"
include "simplbda.mm"
include "mpdan.mm"
include "simp1.mm"
include "ralimi.mm"
include "reximi.mm"
include "biidd.mm"
include "rspcv.mm"
include "mpsyl.mm"
include "dfss3.mm"
include "nnsscn.mm"
include "jctir.mm"
include "elpm2r.mm"
include "nnz.mm"
include "ad2antrl.mm"
include "eqidd.mm"
include "iscau4.mm"
include "mpidan.mm"
include "wi.mm"
include "simprl.mm"
include "eluznn.mm"
include "sylan.mm"
include "dmmptd.mm"
include "eleq2d.mm"
include "biimpar.mm"
include "a1d.mm"
include "idd.mm"
include "3anim123d.mm"
include "sylan2.mm"
include "anassrs.mm"
include "ralimdva.mm"
include "syldan.mm"
include "reximdva.mm"
include "ralimdv.mm"
include "mpd.mm"
include "simprr.mm"
include "sselda.mm"
include "iftrue.mm"
include "adantl.mm"
include "fvex.mm"
include "syl6eqel.mm"
include "weq.mm"
include "eleq1.mm"
include "fveq2.mm"
include "ifbieq1d.mm"
include "fvmptg.mm"
include "eqtrd.mm"
include "cin.mm"
include "elind.mm"
include "eqeq12d.mm"
include "elin.mm"
include "sylbi.mm"
include "vtoclga.mm"
include "mpbir2and.mm"
include "expr.mm"
include "syl5bir.mm"
include "rexlimdva.mm"
include "wb.mm"
include "caucfil.mm"
include "mpbid.mm"
include "cmetcvg.mm"
include "eqnetrd.mm"
include "n0.mm"
include "sylib.mm"
include "lmflf.mm"
include "lmcl.mm"
include "lmmbr3.mm"
include "biimpa.mm"
include "simp3d.mm"
include "r19.26.mm"
include "rexanuz2.mm"
include "ad2ant2lr.mm"
include "simprr2.mm"
include "eqeltrrd.mm"
include "oveq1d.mm"
include "simprr3.mm"
include "eqbrtrrd.mm"
include "3jca.mm"
include "ex.mm"
include "mpand.mm"
include "mpbir3and.mm"
include "lmrel.mm"
include "releldmi.mm"
include "sylbird.mm"
include "exlimdv.mm"

theorem cmetcaulem
  let wph: wff ph
  let vx: setvar x
  let cD: class D
  let cP: class P
  let cF: class F
  let cG: class G
  let cJ: class J
  let cX: class X
  let vj: setvar j
  let vk: setvar k
  let vm: setvar m
  let vw: setvar w
  let vy: setvar y
  let vz: setvar z
  assume cmetcau.1: |- J = ( MetOpen ` D )
  assume cmetcau.3: |- ( ph -> D e. ( CMet ` X ) )
  assume cmetcau.4: |- ( ph -> P e. X )
  assume cmetcau.5: |- ( ph -> F e. ( Cau ` D ) )
  assume cmetcau.6: |- G = ( x e. NN |-> if ( x e. dom F , ( F ` x ) , P ) )

  disjoint D x
  disjoint F x
  disjoint P x
  disjoint J x
  disjoint ph x
  disjoint X x
  disjoint j k
  disjoint j m
  disjoint j w
  disjoint j x
  disjoint j y
  disjoint j z
  disjoint D j
  disjoint k m
  disjoint k w
  disjoint k x
  disjoint k y
  disjoint k z
  disjoint D k
  disjoint m w
  disjoint m x
  disjoint m y
  disjoint m z
  disjoint D m
  disjoint w x
  disjoint w y
  disjoint w z
  disjoint D w
  disjoint x y
  disjoint x z
  disjoint y z
  disjoint D y
  disjoint D z
  disjoint F j
  disjoint F k
  disjoint F m
  disjoint F w
  disjoint F y
  disjoint F z
  disjoint G j
  disjoint G k
  disjoint G m
  disjoint G y
  disjoint G z
  disjoint J j
  disjoint J k
  disjoint J y
  disjoint J z
  disjoint j ph
  disjoint k ph
  disjoint m ph
  disjoint ph y
  disjoint ph z
  disjoint X j
  disjoint X k
  disjoint X m
  disjoint X w
  disjoint X y
  disjoint X z
  assert |- ( ph -> F e. dom ( ~~>t ` J ) )

  proof
    wph
    vy
    cv
    #
    cG
    cJ
    cn
    cuz
    cn
    cima
    #
    cfg
    co
    #
    cflf
    co
    cfv
    #
    wcel
    #
    vy
    wex
    #
    cF
    cJ
    clm
    cfv
    #
    cdm
    wcel
    #
    wph
    @3
    c0
    wne
    @5
    wph
    @3
    cJ
    @1
    cX
    cG
    cfm
    co
    #
    cfv
    #
    cflim
    co
    #
    c0
    wph
    @3
    cJ
    @2
    @8
    cfv
    #
    cflim
    co
    #
    @10
    wph
    cJ
    cX
    ctopon
    cfv
    wcel
    #
    @2
    cn
    cfil
    cfv
    wcel
    #
    cn
    cX
    cG
    wf
    #
    @3
    @12
    wceq
    wph
    cD
    cX
    cxmt
    cfv
    wcel
    #
    @13
    wph
    cD
    cX
    cme
    cfv
    wcel
    #
    @16
    wph
    cD
    cX
    cms
    cfv
    wcel
    #
    @17
    cmetcau.3
    cD
    cX
    cmetmet
    syl
    cD
    cX
    metxmet
    syl
    #
    cD
    cJ
    cX
    cmetcau.1
    mopntopon
    syl
    #
    wph
    @1
    cn
    cfbas
    cfv
    wcel
    #
    @14
    c1
    cz
    wcel
    #
    @21
    wph
    1z
    c1
    cn
    nnuz
    uzfbas
    mp1i
    #
    @1
    cn
    fgcl
    syl
    wph
    vx
    cn
    vx
    cv
    #
    cF
    cdm
    #
    wcel
    #
    @24
    cF
    cfv
    #
    cP
    cif
    #
    cX
    cG
    wph
    @24
    cn
    wcel
    #
    wa
    #
    @26
    @27
    cP
    cX
    @30
    @25
    cX
    @24
    cF
    wph
    @25
    cX
    cF
    wf
    #
    @29
    wph
    cX
    cms
    cdm
    #
    wcel
    #
    cc
    cvv
    wcel
    #
    cF
    cX
    cc
    cpm
    co
    #
    wcel
    #
    @31
    wph
    @18
    @33
    cmetcau.3
    cD
    cX
    cms
    elfvdm
    syl
    #
    @34
    wph
    cnex
    a1i
    #
    wph
    @16
    cF
    cD
    cca
    cfv
    #
    wcel
    #
    @36
    @19
    cmetcau.5
    cD
    cF
    cX
    caufpm
    syl2anc
    #
    @33
    @34
    wa
    @36
    @31
    @25
    cc
    wss
    cX
    cc
    cF
    @32
    cvv
    elpm2g
    simprbda
    syl21anc
    adantr
    ffvelrnda
    wph
    cP
    cX
    wcel
    @29
    @26
    wn
    cmetcau.4
    ad2antrr
    ifclda
    #
    cmetcau.6
    fmptd
    #
    cG
    cJ
    @2
    cX
    cn
    flfval
    syl3anc
    wph
    @9
    @11
    cJ
    cflim
    wph
    @33
    @21
    @15
    @9
    @11
    wceq
    @37
    @23
    @43
    @1
    @32
    cG
    @2
    cX
    cn
    @2
    eqid
    #
    fmfg
    syl3anc
    oveq2d
    eqtr4d
    wph
    @18
    @9
    cD
    ccfil
    cfv
    wcel
    #
    @10
    c0
    wne
    cmetcau.3
    wph
    cG
    @39
    wcel
    #
    @45
    wph
    vk
    cv
    #
    @25
    wcel
    #
    vk
    vj
    cv
    #
    cuz
    cfv
    #
    wral
    #
    vj
    cn
    wrex
    #
    @46
    c1
    crp
    wcel
    wph
    @52
    vz
    crp
    wral
    #
    @52
    1rp
    wph
    @48
    @47
    cF
    cfv
    #
    cX
    wcel
    #
    @54
    vw
    cv
    cF
    cfv
    cD
    co
    vz
    cv
    #
    clt
    wbr
    vw
    @47
    cuz
    cfv
    wral
    #
    w3a
    #
    vk
    @50
    wral
    #
    vj
    cn
    wrex
    #
    vz
    crp
    wral
    #
    @53
    wph
    @40
    @61
    cmetcau.5
    wph
    @40
    @36
    @61
    wph
    vz
    cD
    vj
    vk
    vw
    cF
    c1
    cX
    cn
    nnuz
    @19
    wph
    1zzd
    #
    iscau3
    simplbda
    mpdan
    @60
    @52
    vz
    crp
    @59
    @51
    vj
    cn
    @58
    @48
    vk
    @50
    @48
    @55
    @57
    simp1
    ralimi
    reximi
    ralimi
    syl
    #
    @52
    @52
    vz
    c1
    crp
    @56
    c1
    wceq
    @52
    biidd
    rspcv
    mpsyl
    wph
    @51
    @46
    vj
    cn
    @51
    @50
    @25
    wss
    #
    wph
    @49
    cn
    wcel
    #
    wa
    #
    @46
    vk
    @50
    @25
    dfss3
    wph
    @65
    @64
    @46
    wph
    @65
    @64
    wa
    #
    wa
    #
    @46
    cG
    @35
    wcel
    #
    @47
    cG
    cdm
    #
    wcel
    #
    @55
    @54
    vm
    cv
    #
    cF
    cfv
    #
    cD
    co
    @56
    clt
    wbr
    #
    w3a
    #
    vk
    @72
    cuz
    cfv
    #
    wral
    #
    vm
    @50
    wrex
    #
    vz
    crp
    wral
    #
    wph
    @69
    @67
    wph
    @33
    @34
    @15
    cn
    cc
    wss
    #
    wa
    @69
    @37
    @38
    wph
    @15
    @80
    @43
    nnsscn
    jctir
    cX
    cc
    cn
    cG
    @32
    cvv
    elpm2r
    syl21anc
    adantr
    @68
    @48
    @55
    @74
    w3a
    #
    vk
    @76
    wral
    #
    vm
    @50
    wrex
    #
    vz
    crp
    wral
    #
    @79
    wph
    @67
    @40
    @84
    cmetcau.5
    @68
    @40
    @36
    @84
    @68
    vz
    @54
    @73
    cD
    vm
    vk
    cF
    @49
    cX
    @50
    @50
    eqid
    #
    wph
    @16
    @67
    @19
    adantr
    #
    @65
    @49
    cz
    wcel
    wph
    @64
    @49
    nnz
    ad2antrl
    #
    @68
    @47
    @50
    wcel
    #
    wa
    #
    @54
    eqidd
    @68
    @72
    @50
    wcel
    #
    wa
    #
    @73
    eqidd
    iscau4
    simplbda
    mpidan
    @68
    @83
    @78
    vz
    crp
    @68
    @82
    @77
    vm
    @50
    @68
    @90
    @72
    cn
    wcel
    #
    @82
    @77
    wi
    @68
    @65
    @90
    @92
    wph
    @65
    @64
    simprl
    #
    @72
    @49
    eluznn
    sylan
    #
    @68
    @92
    wa
    @81
    @75
    vk
    @76
    @68
    @92
    @47
    @76
    wcel
    #
    @81
    @75
    wi
    #
    @92
    @95
    wa
    @68
    @47
    cn
    wcel
    #
    @96
    @47
    @72
    eluznn
    @68
    @97
    wa
    #
    @48
    @71
    @55
    @55
    @74
    @74
    @98
    @71
    @48
    @68
    @71
    @97
    @68
    @70
    cn
    @47
    wph
    @70
    cn
    wceq
    @67
    wph
    vx
    cG
    cn
    @28
    cX
    cmetcau.6
    @42
    dmmptd
    adantr
    eleq2d
    biimpar
    a1d
    @98
    @55
    idd
    @98
    @74
    idd
    3anim123d
    sylan2
    anassrs
    ralimdva
    syldan
    reximdva
    ralimdv
    mpd
    @68
    vz
    @54
    @73
    cD
    vm
    vk
    cG
    @49
    cX
    @50
    @85
    @86
    @87
    @89
    @97
    @48
    @47
    cG
    cfv
    #
    @54
    wceq
    #
    @68
    @65
    @88
    @97
    @93
    @47
    @49
    eluznn
    #
    sylan
    @68
    @50
    @25
    @47
    wph
    @65
    @64
    simprr
    #
    sselda
    @97
    @48
    wa
    #
    @99
    @48
    @54
    cP
    cif
    #
    @54
    @97
    @48
    @104
    cvv
    wcel
    @99
    @104
    wceq
    @103
    @104
    @54
    cvv
    @48
    @104
    @54
    wceq
    @97
    @48
    @54
    cP
    iftrue
    adantl
    #
    @47
    cF
    fvex
    syl6eqel
    vx
    @47
    @28
    @104
    cn
    cvv
    cG
    vx
    vk
    weq
    @26
    @48
    @27
    @54
    cP
    @24
    @47
    @25
    eleq1
    @24
    @47
    cF
    fveq2
    ifbieq1d
    cmetcau.6
    fvmptg
    syldan
    @105
    eqtrd
    #
    syl2anc
    @91
    @72
    cn
    @25
    cin
    #
    wcel
    @72
    cG
    cfv
    #
    @73
    wceq
    #
    @91
    cn
    @25
    @72
    @94
    @68
    @50
    @25
    @72
    @102
    sselda
    elind
    @100
    @109
    vk
    @72
    @107
    vk
    vm
    weq
    @99
    @108
    @54
    @73
    @47
    @72
    cG
    fveq2
    @47
    @72
    cF
    fveq2
    eqeq12d
    @47
    @107
    wcel
    @103
    @100
    @47
    cn
    @25
    elin
    @106
    sylbi
    vtoclga
    syl
    iscau4
    mpbir2and
    expr
    syl5bir
    rexlimdva
    mpd
    wph
    @16
    @22
    @15
    @46
    @45
    wb
    @19
    @62
    @43
    cD
    cG
    @9
    c1
    cX
    cn
    nnuz
    @9
    eqid
    caucfil
    syl3anc
    mpbid
    cD
    @9
    cJ
    cX
    cmetcau.1
    cmetcvg
    syl2anc
    eqnetrd
    vy
    @3
    n0
    sylib
    wph
    @4
    @7
    vy
    wph
    @4
    cG
    @0
    @6
    wbr
    #
    @7
    wph
    @13
    @22
    @15
    @110
    @4
    wb
    @20
    @62
    @43
    @0
    cG
    cJ
    @2
    c1
    cX
    cn
    nnuz
    @44
    lmflf
    syl3anc
    wph
    @110
    @7
    wph
    @110
    wa
    #
    cF
    @0
    @6
    wbr
    #
    @7
    @111
    @112
    @36
    @0
    cX
    wcel
    #
    @48
    @55
    @54
    @0
    cD
    co
    #
    @56
    clt
    wbr
    #
    w3a
    #
    vk
    @50
    wral
    #
    vj
    cn
    wrex
    #
    vz
    crp
    wral
    #
    wph
    @36
    @110
    @41
    adantr
    wph
    @13
    @110
    @113
    @20
    @0
    cG
    cJ
    cX
    lmcl
    sylan
    @111
    @71
    @99
    cX
    wcel
    #
    @99
    @0
    cD
    co
    #
    @56
    clt
    wbr
    #
    w3a
    #
    vk
    @50
    wral
    vj
    cn
    wrex
    #
    vz
    crp
    wral
    #
    @119
    @111
    @69
    @113
    @125
    wph
    @110
    @69
    @113
    @125
    w3a
    wph
    vz
    cD
    @0
    vj
    vk
    cG
    cJ
    c1
    cX
    cn
    cmetcau.1
    @19
    nnuz
    @62
    lmmbr3
    biimpa
    simp3d
    wph
    @125
    @119
    wi
    @110
    wph
    @53
    @125
    @119
    @63
    @53
    @125
    wa
    @52
    @124
    wa
    #
    vz
    crp
    wral
    wph
    @119
    @52
    @124
    vz
    crp
    r19.26
    wph
    @126
    @118
    vz
    crp
    @126
    @48
    @123
    wa
    #
    vk
    @50
    wral
    #
    vj
    cn
    wrex
    wph
    @118
    @48
    @123
    vj
    vk
    c1
    cn
    nnuz
    rexanuz2
    wph
    @128
    @117
    vj
    cn
    @66
    @127
    @116
    vk
    @50
    wph
    @65
    @88
    @127
    @116
    wi
    #
    @65
    @88
    wa
    wph
    @97
    @129
    @101
    wph
    @97
    wa
    #
    @127
    @116
    @130
    @127
    wa
    #
    @48
    @55
    @115
    @130
    @48
    @123
    simprl
    @131
    @99
    @54
    cX
    @97
    @48
    @100
    wph
    @123
    @106
    ad2ant2lr
    #
    @71
    @120
    @122
    @48
    @130
    simprr2
    eqeltrrd
    @131
    @121
    @114
    @56
    clt
    @131
    @99
    @54
    @0
    cD
    @132
    oveq1d
    @71
    @120
    @122
    @48
    @130
    simprr3
    eqbrtrrd
    3jca
    ex
    sylan2
    anassrs
    ralimdva
    reximdva
    syl5bir
    ralimdv
    syl5bir
    mpand
    adantr
    mpd
    @111
    vz
    cD
    @0
    vj
    vk
    cF
    cJ
    c1
    cX
    cn
    cmetcau.1
    wph
    @16
    @110
    @19
    adantr
    nnuz
    @111
    1zzd
    lmmbr3
    mpbir3and
    cF
    @0
    @6
    cJ
    lmrel
    releldmi
    syl
    ex
    sylbird
    exlimdv
    mpd
end
