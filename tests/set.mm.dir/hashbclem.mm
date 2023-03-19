include "chash.mm"
include "cfv.mm"
include "cbc.mm"
include "co.mm"
include "c1.mm"
include "cmin.mm"
include "caddc.mm"
include "wel.mm"
include "wn.mm"
include "cv.mm"
include "wceq.mm"
include "wa.mm"
include "csn.mm"
include "cun.mm"
include "cpw.mm"
include "crab.mm"
include "cz.mm"
include "wcel.mm"
include "wral.mm"
include "oveq2.mm"
include "eqeq2.mm"
include "rabbidv.mm"
include "fveq2d.mm"
include "eqeq12d.mm"
include "rspcv.mm"
include "sylc.mm"
include "wss.mm"
include "ssun1.mm"
include "sspwb.mm"
include "mpbi.mm"
include "sseli.mm"
include "adantl.mm"
include "elpwi.mm"
include "ssneld.mm"
include "mpan9.mm"
include "jca.mm"
include "uncom.mm"
include "syl6sseq.mm"
include "adantr.mm"
include "cin.mm"
include "c0.mm"
include "wb.mm"
include "simpr.mm"
include "disjsn.mm"
include "sylibr.mm"
include "disjssun.mm"
include "syl.mm"
include "mpbid.mm"
include "vex.mm"
include "elpw.mm"
include "impbida.mm"
include "anbi1d.mm"
include "anass.mm"
include "syl6bb.mm"
include "rabbidva2.mm"
include "eqtrd.mm"
include "peano2zm.mm"
include "cen.mm"
include "wbr.mm"
include "cdif.mm"
include "cfn.mm"
include "cvv.mm"
include "pwfi.mm"
include "sylib.mm"
include "rabexg.mm"
include "snfi.mm"
include "unfi.mm"
include "sylancl.mm"
include "ssrab2.mm"
include "ssfi.mm"
include "elex.mm"
include "fveq2.mm"
include "eqeq1d.mm"
include "elrab.mm"
include "ad2antrl.mm"
include "unss1.mm"
include "snex.mm"
include "unex.mm"
include "syl2anc.mm"
include "a1i.mm"
include "ssneldd.mm"
include "hashun.mm"
include "syl3anc.mm"
include "simprr.mm"
include "hashsng.mm"
include "ax-mp.mm"
include "oveq12d.mm"
include "cc.mm"
include "zcnd.mm"
include "ax-1cn.mm"
include "npcan.mm"
include "3eqtrd.mm"
include "ssun2.mm"
include "snss.mm"
include "mpbir.mm"
include "jctil.mm"
include "eleq2.mm"
include "anbi12d.mm"
include "sylanbrc.mm"
include "ex.mm"
include "syl5bi.mm"
include "ssundif.mm"
include "difexg.mm"
include "cn0.mm"
include "hashcl.mm"
include "nn0cnd.mm"
include "pncan.mm"
include "undif1.mm"
include "simprrl.mm"
include "snssd.mm"
include "ssequn2.mm"
include "syl5eq.mm"
include "incom.mm"
include "disjdif.mm"
include "eqtri.mm"
include "oveq2i.mm"
include "syl6eq.mm"
include "simprrr.mm"
include "3eqtr3d.mm"
include "oveq1d.mm"
include "eqtr3d.mm"
include "anbi12i.mm"
include "w3a.mm"
include "simp3rl.mm"
include "3adant3.mm"
include "uneqdifeq.mm"
include "bicomd.mm"
include "eqcom.mm"
include "eqeq1i.mm"
include "bitri.mm"
include "3bitr4g.mm"
include "3expib.mm"
include "en3d.mm"
include "hashen.mm"
include "mpbird.mm"
include "bcpasc.mm"
include "eqtr4d.mm"
include "wo.mm"
include "pm2.1.mm"
include "biantrur.mm"
include "andir.mm"
include "rabbii.mm"
include "unrab.mm"
include "eqtr4i.mm"
include "fveq2i.mm"
include "inrab.mm"
include "simprl.mm"
include "simpll.mm"
include "pm2.65i.mm"
include "rgenw.mm"
include "rabeq0.mm"
include "3eqtr4d.mm"

theorem hashbclem
  let wph: wff ph
  let vx: setvar x
  let vz: setvar z
  let cA: class A
  let vj: setvar j
  let cK: class K
  let vk: setvar k
  let vu: setvar u
  let vv: setvar v
  let vw: setvar w
  let vy: setvar y
  assume hashbc.1: |- ( ph -> A e. Fin )
  assume hashbc.2: |- ( ph -> -. z e. A )
  assume hashbc.3: |- ( ph -> A. j e. ZZ ( ( # ` A ) _C j ) = ( # ` { x e. ~P A | ( # ` x ) = j } ) )
  assume hashbc.4: |- ( ph -> K e. ZZ )

  disjoint j x
  disjoint j z
  disjoint A j
  disjoint x z
  disjoint A x
  disjoint A z
  disjoint K j
  disjoint K x
  disjoint ph x
  disjoint j k
  disjoint j u
  disjoint j v
  disjoint j w
  disjoint j y
  disjoint k u
  disjoint k v
  disjoint k w
  disjoint k x
  disjoint k y
  disjoint k z
  disjoint A k
  disjoint u v
  disjoint u w
  disjoint u x
  disjoint u y
  disjoint u z
  disjoint A u
  disjoint v w
  disjoint v x
  disjoint v y
  disjoint v z
  disjoint A v
  disjoint w x
  disjoint w y
  disjoint w z
  disjoint A w
  disjoint x y
  disjoint y z
  disjoint A y
  disjoint K k
  disjoint K u
  disjoint K v
  disjoint ph u
  disjoint ph v
  assert |- ( ph -> ( ( # ` ( A u. { z } ) ) _C K ) = ( # ` { x e. ~P ( A u. { z } ) | ( # ` x ) = K } ) )

  proof
    wph
    cA
    chash
    cfv
    #
    cK
    cbc
    co
    #
    @0
    cK
    c1
    cmin
    co
    #
    cbc
    co
    #
    caddc
    co
    #
    vz
    vx
    wel
    #
    wn
    #
    vx
    cv
    #
    chash
    cfv
    #
    cK
    wceq
    #
    wa
    #
    vx
    cA
    vz
    cv
    #
    csn
    #
    cun
    #
    cpw
    #
    crab
    #
    chash
    cfv
    #
    @5
    @9
    wa
    #
    vx
    @14
    crab
    #
    chash
    cfv
    #
    caddc
    co
    #
    @13
    chash
    cfv
    #
    cK
    cbc
    co
    #
    @9
    vx
    @14
    crab
    #
    chash
    cfv
    #
    wph
    @1
    @16
    @3
    @19
    caddc
    wph
    @1
    @9
    vx
    cA
    cpw
    #
    crab
    #
    chash
    cfv
    #
    @16
    wph
    cK
    cz
    wcel
    #
    @0
    vj
    cv
    #
    cbc
    co
    #
    @8
    @29
    wceq
    #
    vx
    @25
    crab
    #
    chash
    cfv
    #
    wceq
    #
    vj
    cz
    wral
    #
    @1
    @27
    wceq
    #
    hashbc.4
    hashbc.3
    @34
    @36
    vj
    cK
    cz
    @29
    cK
    wceq
    #
    @30
    @1
    @33
    @27
    @29
    cK
    @0
    cbc
    oveq2
    @37
    @32
    @26
    chash
    @37
    @31
    @9
    vx
    @25
    @29
    cK
    @8
    eqeq2
    rabbidv
    fveq2d
    eqeq12d
    rspcv
    sylc
    wph
    @26
    @15
    chash
    wph
    @9
    @10
    vx
    @25
    @14
    wph
    @7
    @25
    wcel
    #
    @9
    wa
    @7
    @14
    wcel
    #
    @6
    wa
    #
    @9
    wa
    @39
    @10
    wa
    wph
    @38
    @40
    @9
    wph
    @38
    @40
    wph
    @38
    wa
    @39
    @6
    @38
    @39
    wph
    @25
    @14
    @7
    cA
    @13
    wss
    @25
    @14
    wss
    cA
    @12
    ssun1
    cA
    @13
    sspwb
    mpbi
    sseli
    adantl
    wph
    @11
    cA
    wcel
    wn
    #
    @38
    @6
    hashbc.2
    @38
    @7
    cA
    @11
    @7
    cA
    elpwi
    ssneld
    mpan9
    jca
    @40
    @38
    wph
    @40
    @7
    cA
    wss
    #
    @38
    @40
    @7
    @12
    cA
    cun
    #
    wss
    #
    @42
    @39
    @44
    @6
    @39
    @7
    @13
    @43
    @7
    @13
    elpwi
    cA
    @12
    uncom
    #
    syl6sseq
    adantr
    @40
    @7
    @12
    cin
    c0
    wceq
    #
    @44
    @42
    wb
    @40
    @6
    @46
    @39
    @6
    simpr
    @7
    @11
    disjsn
    sylibr
    @7
    @12
    cA
    disjssun
    syl
    mpbid
    @7
    cA
    vx
    vex
    elpw
    sylibr
    adantl
    impbida
    anbi1d
    @39
    @6
    @9
    anass
    syl6bb
    rabbidva2
    fveq2d
    eqtrd
    wph
    @3
    @8
    @2
    wceq
    #
    vx
    @25
    crab
    #
    chash
    cfv
    #
    @19
    wph
    @2
    cz
    wcel
    #
    @35
    @3
    @49
    wceq
    #
    wph
    @28
    @50
    hashbc.4
    cK
    peano2zm
    syl
    hashbc.3
    @34
    @51
    vj
    @2
    cz
    @29
    @2
    wceq
    #
    @30
    @3
    @33
    @49
    @29
    @2
    @0
    cbc
    oveq2
    @52
    @32
    @48
    chash
    @52
    @31
    @47
    vx
    @25
    @29
    @2
    @8
    eqeq2
    rabbidv
    fveq2d
    eqeq12d
    rspcv
    sylc
    wph
    @49
    @19
    wceq
    #
    @48
    @18
    cen
    wbr
    #
    wph
    vu
    vv
    @48
    @18
    vu
    cv
    #
    @12
    cun
    #
    vv
    cv
    #
    @12
    cdif
    #
    wph
    @25
    cfn
    wcel
    #
    @48
    cvv
    wcel
    wph
    cA
    cfn
    wcel
    #
    @59
    hashbc.1
    cA
    pwfi
    sylib
    #
    @47
    vx
    @25
    cfn
    rabexg
    syl
    wph
    @18
    cfn
    wcel
    #
    @18
    cvv
    wcel
    wph
    @14
    cfn
    wcel
    #
    @18
    @14
    wss
    @62
    wph
    @13
    cfn
    wcel
    #
    @63
    wph
    @60
    @12
    cfn
    wcel
    #
    @64
    hashbc.1
    @11
    snfi
    #
    cA
    @12
    unfi
    sylancl
    @13
    pwfi
    sylib
    #
    @17
    vx
    @14
    ssrab2
    @14
    @18
    ssfi
    sylancl
    #
    @18
    cfn
    elex
    syl
    @55
    @48
    wcel
    #
    @55
    @25
    wcel
    #
    @55
    chash
    cfv
    #
    @2
    wceq
    #
    wa
    #
    wph
    @56
    @18
    wcel
    #
    @47
    @72
    vx
    @55
    @25
    @7
    @55
    wceq
    @8
    @71
    @2
    @7
    @55
    chash
    fveq2
    eqeq1d
    elrab
    #
    wph
    @73
    @74
    wph
    @73
    wa
    #
    @56
    @14
    wcel
    #
    @11
    @56
    wcel
    #
    @56
    chash
    cfv
    #
    cK
    wceq
    #
    wa
    #
    @74
    @76
    @56
    @13
    wss
    #
    @77
    @76
    @55
    cA
    wss
    #
    @82
    @70
    @83
    wph
    @72
    @55
    cA
    elpwi
    ad2antrl
    #
    @55
    cA
    @12
    unss1
    syl
    @56
    @13
    @55
    @12
    vu
    vex
    @11
    snex
    unex
    elpw
    sylibr
    @76
    @80
    @78
    @76
    @79
    @71
    @12
    chash
    cfv
    #
    caddc
    co
    #
    @2
    c1
    caddc
    co
    #
    cK
    @76
    @55
    cfn
    wcel
    #
    @65
    @55
    @12
    cin
    #
    c0
    wceq
    #
    @79
    @86
    wceq
    @76
    @60
    @83
    @88
    wph
    @60
    @73
    hashbc.1
    adantr
    @84
    cA
    @55
    ssfi
    syl2anc
    @65
    @76
    @66
    a1i
    @76
    vz
    vu
    wel
    wn
    @90
    @76
    @55
    cA
    @11
    @84
    wph
    @41
    @73
    hashbc.2
    adantr
    ssneldd
    @55
    @11
    disjsn
    sylibr
    #
    @55
    @12
    hashun
    syl3anc
    @76
    @71
    @2
    @85
    c1
    caddc
    wph
    @70
    @72
    simprr
    @85
    c1
    wceq
    #
    @76
    @11
    cvv
    wcel
    @92
    vz
    vex
    #
    @11
    cvv
    hashsng
    ax-mp
    #
    a1i
    oveq12d
    @76
    cK
    cc
    wcel
    c1
    cc
    wcel
    #
    @87
    cK
    wceq
    @76
    cK
    wph
    @28
    @73
    hashbc.4
    adantr
    zcnd
    ax-1cn
    cK
    c1
    npcan
    sylancl
    3eqtrd
    @78
    @12
    @56
    wss
    @12
    @55
    ssun2
    @11
    @56
    @93
    snss
    mpbir
    jctil
    @17
    @81
    vx
    @56
    @14
    @7
    @56
    wceq
    #
    @5
    @78
    @9
    @80
    @7
    @56
    @11
    eleq2
    @96
    @8
    @79
    cK
    @7
    @56
    chash
    fveq2
    eqeq1d
    anbi12d
    elrab
    sylanbrc
    ex
    syl5bi
    @57
    @18
    wcel
    #
    @57
    @14
    wcel
    #
    vz
    vv
    wel
    #
    @57
    chash
    cfv
    #
    cK
    wceq
    #
    wa
    #
    wa
    #
    wph
    @58
    @48
    wcel
    #
    @17
    @102
    vx
    @57
    @14
    @7
    @57
    wceq
    #
    @5
    @99
    @9
    @101
    @7
    @57
    @11
    eleq2
    @105
    @8
    @100
    cK
    @7
    @57
    chash
    fveq2
    eqeq1d
    anbi12d
    elrab
    #
    wph
    @103
    @104
    wph
    @103
    wa
    #
    @58
    @25
    wcel
    #
    @58
    chash
    cfv
    #
    @2
    wceq
    #
    @104
    @107
    @58
    cA
    wss
    #
    @108
    @107
    @57
    @43
    wss
    @111
    @107
    @57
    @13
    @43
    @98
    @57
    @13
    wss
    wph
    @102
    @57
    @13
    elpwi
    ad2antrl
    @45
    syl6sseq
    @57
    @12
    cA
    ssundif
    sylib
    #
    @58
    cA
    @57
    cvv
    wcel
    @58
    cvv
    wcel
    vv
    vex
    @57
    @12
    cvv
    difexg
    ax-mp
    elpw
    sylibr
    @107
    @109
    c1
    caddc
    co
    #
    c1
    cmin
    co
    #
    @109
    @2
    @107
    @109
    cc
    wcel
    @95
    @114
    @109
    wceq
    @107
    @109
    @107
    @58
    cfn
    wcel
    #
    @109
    cn0
    wcel
    @107
    @60
    @111
    @115
    wph
    @60
    @103
    hashbc.1
    adantr
    @112
    cA
    @58
    ssfi
    syl2anc
    #
    @58
    hashcl
    syl
    nn0cnd
    ax-1cn
    @109
    c1
    pncan
    sylancl
    @107
    @113
    cK
    c1
    cmin
    @107
    @58
    @12
    cun
    #
    chash
    cfv
    #
    @100
    @113
    cK
    @107
    @117
    @57
    chash
    @107
    @117
    @57
    @12
    cun
    #
    @57
    @57
    @12
    undif1
    @107
    @12
    @57
    wss
    #
    @119
    @57
    wceq
    @107
    @11
    @57
    wph
    @98
    @99
    @101
    simprrl
    snssd
    @12
    @57
    ssequn2
    sylib
    syl5eq
    fveq2d
    @107
    @118
    @109
    @85
    caddc
    co
    #
    @113
    @107
    @115
    @65
    @58
    @12
    cin
    #
    c0
    wceq
    #
    @118
    @121
    wceq
    @116
    @65
    @107
    @66
    a1i
    @123
    @107
    @122
    @12
    @58
    cin
    c0
    @58
    @12
    incom
    @12
    @57
    disjdif
    eqtri
    a1i
    @58
    @12
    hashun
    syl3anc
    @85
    c1
    @109
    caddc
    @94
    oveq2i
    syl6eq
    wph
    @98
    @99
    @101
    simprrr
    3eqtr3d
    oveq1d
    eqtr3d
    @47
    @110
    vx
    @58
    @25
    @7
    @58
    wceq
    @8
    @109
    @2
    @7
    @58
    chash
    fveq2
    eqeq1d
    elrab
    sylanbrc
    ex
    syl5bi
    @69
    @97
    wa
    @73
    @103
    wa
    wph
    @55
    @58
    wceq
    #
    @57
    @56
    wceq
    #
    wb
    #
    @69
    @73
    @97
    @103
    @75
    @106
    anbi12i
    wph
    @73
    @103
    @126
    wph
    @73
    @103
    w3a
    #
    @58
    @55
    wceq
    #
    @12
    @55
    cun
    #
    @57
    wceq
    #
    @124
    @125
    @127
    @130
    @128
    @127
    @120
    @12
    @55
    cin
    #
    c0
    wceq
    @130
    @128
    wb
    @127
    @11
    @57
    @99
    @101
    @98
    wph
    @73
    simp3rl
    snssd
    @127
    @131
    @89
    c0
    @12
    @55
    incom
    wph
    @73
    @90
    @103
    @91
    3adant3
    syl5eq
    @12
    @55
    @57
    uneqdifeq
    syl2anc
    bicomd
    @55
    @58
    eqcom
    @125
    @56
    @57
    wceq
    @130
    @57
    @56
    eqcom
    @56
    @129
    @57
    @55
    @12
    uncom
    eqeq1i
    bitri
    3bitr4g
    3expib
    syl5bi
    en3d
    wph
    @48
    cfn
    wcel
    #
    @62
    @53
    @54
    wb
    wph
    @59
    @48
    @25
    wss
    @132
    @61
    @47
    vx
    @25
    ssrab2
    @25
    @48
    ssfi
    sylancl
    @68
    @48
    @18
    hashen
    syl2anc
    mpbird
    eqtrd
    oveq12d
    wph
    @22
    @0
    c1
    caddc
    co
    #
    cK
    cbc
    co
    #
    @4
    wph
    @21
    @133
    cK
    cbc
    wph
    @21
    @0
    @85
    caddc
    co
    #
    @133
    wph
    @60
    @65
    cA
    @12
    cin
    c0
    wceq
    #
    @21
    @135
    wceq
    hashbc.1
    @65
    wph
    @66
    a1i
    wph
    @41
    @136
    hashbc.2
    cA
    @11
    disjsn
    sylibr
    cA
    @12
    hashun
    syl3anc
    @85
    c1
    @0
    caddc
    @94
    oveq2i
    syl6eq
    oveq1d
    wph
    @0
    cn0
    wcel
    #
    @28
    @4
    @134
    wceq
    wph
    @60
    @137
    hashbc.1
    cA
    hashcl
    syl
    hashbc.4
    cK
    @0
    bcpasc
    syl2anc
    eqtr4d
    wph
    @24
    @15
    @18
    cun
    #
    chash
    cfv
    #
    @20
    @23
    @138
    chash
    @23
    @10
    @17
    wo
    #
    vx
    @14
    crab
    @138
    @9
    @140
    vx
    @14
    @9
    @6
    @5
    wo
    #
    @9
    wa
    @140
    @141
    @9
    @5
    pm2.1
    biantrur
    @6
    @5
    @9
    andir
    bitri
    rabbii
    @10
    @17
    vx
    @14
    unrab
    eqtr4i
    fveq2i
    wph
    @15
    cfn
    wcel
    #
    @62
    @15
    @18
    cin
    #
    c0
    wceq
    #
    @139
    @20
    wceq
    wph
    @63
    @15
    @14
    wss
    @142
    @67
    @10
    vx
    @14
    ssrab2
    @14
    @15
    ssfi
    sylancl
    @68
    @144
    wph
    @143
    @10
    @17
    wa
    #
    vx
    @14
    crab
    #
    c0
    @10
    @17
    vx
    @14
    inrab
    @146
    c0
    wceq
    @145
    wn
    #
    vx
    @14
    wral
    @147
    vx
    @14
    @145
    @5
    @10
    @5
    @9
    simprl
    @6
    @9
    @17
    simpll
    pm2.65i
    rgenw
    @145
    vx
    @14
    rabeq0
    mpbir
    eqtri
    a1i
    @15
    @18
    hashun
    syl3anc
    syl5eq
    3eqtr4d
end
