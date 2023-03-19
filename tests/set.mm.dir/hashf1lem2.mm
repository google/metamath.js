include "cv.mm"
include "wf1.mm"
include "cab.mm"
include "wss.mm"
include "csn.mm"
include "cun.mm"
include "chash.mm"
include "cfv.mm"
include "cmin.mm"
include "co.mm"
include "cmul.mm"
include "wceq.mm"
include "ssid.mm"
include "cfn.mm"
include "wcel.mm"
include "wi.mm"
include "cmap.mm"
include "mapfi.mm"
include "syl2anc.mm"
include "wf.mm"
include "f1f.mm"
include "elmapd.mm"
include "syl5ibr.mm"
include "abssdv.mm"
include "ssfi.mm"
include "cres.mm"
include "wa.mm"
include "c0.mm"
include "cc0.mm"
include "sseq1.mm"
include "eleq2.mm"
include "noel.mm"
include "pm2.21i.mm"
include "syl6bi.mm"
include "adantrd.mm"
include "ss0.mm"
include "syl.mm"
include "fveq2d.mm"
include "hash0.mm"
include "syl6eq.mm"
include "fveq2.mm"
include "oveq2d.mm"
include "eqeq12d.mm"
include "imbi12d.mm"
include "imbi2d.mm"
include "anbi1d.mm"
include "abbidv.mm"
include "f1eq1.mm"
include "cbvabv.mm"
include "eqeq2i.mm"
include "ssun1.mm"
include "f1ssres.mm"
include "mpan2.mm"
include "vex.mm"
include "resex.mm"
include "elab.mm"
include "sylibr.mm"
include "pm4.71rd.mm"
include "bicomd.mm"
include "sylbi.mm"
include "cn0.mm"
include "hashcl.mm"
include "nn0cnd.mm"
include "subcld.mm"
include "mul01d.mm"
include "eqcomd.mm"
include "a1d.mm"
include "wn.mm"
include "sstr.mm"
include "mpan.mm"
include "imim1i.mm"
include "caddc.mm"
include "oveq1.mm"
include "wo.mm"
include "elun.mm"
include "elsn.mm"
include "orbi2i.mm"
include "bitri.mm"
include "anbi1i.mm"
include "andir.mm"
include "abbii.mm"
include "unab.mm"
include "eqtr4i.mm"
include "fveq2i.mm"
include "cin.mm"
include "snfi.mm"
include "unfi.mm"
include "sylancl.mm"
include "mapvalg.mm"
include "eqeltrrd.mm"
include "adantl.mm"
include "ss2abi.mm"
include "adantr.mm"
include "inab.mm"
include "simprlr.mm"
include "wne.mm"
include "wex.mm"
include "abn0.mm"
include "simprl.mm"
include "simpll.mm"
include "exlimiv.mm"
include "necon1bi.mm"
include "syl5eq.mm"
include "hashun.mm"
include "syl3anc.mm"
include "simpr.mm"
include "unssbd.mm"
include "snss.mm"
include "sylib.mm"
include "cc.mm"
include "pncan2d.mm"
include "crn.mm"
include "cdif.mm"
include "cen.mm"
include "wbr.mm"
include "cvv.mm"
include "wf1o.mm"
include "f1f1orn.mm"
include "f1oen3g.mm"
include "sylancr.mm"
include "hasheni.mm"
include "c1.mm"
include "cle.mm"
include "hashf1lem1.mm"
include "oveq12d.mm"
include "frn.mm"
include "diffi.mm"
include "disjdif.mm"
include "a1i.mm"
include "undif.mm"
include "3eqtr2d.mm"
include "oveq1d.mm"
include "eqtr3d.mm"
include "sylan2.mm"
include "eqtrd.mm"
include "hashunsng.mm"
include "ax-mp.mm"
include "ad2antrl.mm"
include "simprll.mm"
include "1cnd.mm"
include "adddid.mm"
include "mulid1d.mm"
include "3eqtrd.mm"
include "expr.mm"
include "a2d.mm"
include "syl5.mm"
include "expcom.mm"
include "findcard2s.mm"
include "mpcom.mm"
include "mpi.mm"

theorem hashf1lem2
  let wph: wff ph
  let vz: setvar z
  let cA: class A
  let cB: class B
  let vf: setvar f
  let va: setvar a
  let vg: setvar g
  let vx: setvar x
  let vy: setvar y
  let cF: class F
  assume hashf1lem2.1: |- ( ph -> A e. Fin )
  assume hashf1lem2.2: |- ( ph -> B e. Fin )
  assume hashf1lem2.3: |- ( ph -> -. z e. A )
  assume hashf1lem2.4: |- ( ph -> ( ( # ` A ) + 1 ) <_ ( # ` B ) )

  disjoint f z
  disjoint A f
  disjoint B f
  disjoint f ph
  disjoint a f
  disjoint a g
  disjoint a x
  disjoint a y
  disjoint a z
  disjoint f g
  disjoint f x
  disjoint f y
  disjoint g x
  disjoint g y
  disjoint g z
  disjoint x y
  disjoint x z
  disjoint y z
  disjoint A a
  disjoint A g
  disjoint A x
  disjoint A y
  disjoint B a
  disjoint B g
  disjoint B x
  disjoint B y
  disjoint a ph
  disjoint g ph
  disjoint ph x
  disjoint ph y
  disjoint F f
  disjoint F g
  disjoint F x
  disjoint F y
  assert |- ( ph -> ( # ` { f | f : ( A u. { z } ) -1-1-> B } ) = ( ( ( # ` B ) - ( # ` A ) ) x. ( # ` { f | f : A -1-1-> B } ) ) )

  proof
    wph
    cA
    cB
    vf
    cv
    #
    wf1
    #
    vf
    cab
    #
    @2
    wss
    #
    cA
    vz
    cv
    #
    csn
    #
    cun
    #
    cB
    @0
    wf1
    #
    vf
    cab
    #
    chash
    cfv
    #
    cB
    chash
    cfv
    #
    cA
    chash
    cfv
    #
    cmin
    co
    #
    @2
    chash
    cfv
    #
    cmul
    co
    #
    wceq
    #
    @2
    ssid
    @2
    cfn
    wcel
    #
    wph
    @3
    @15
    wi
    #
    wph
    cB
    cA
    cmap
    co
    #
    cfn
    wcel
    #
    @2
    @18
    wss
    @16
    wph
    cB
    cfn
    wcel
    #
    cA
    cfn
    wcel
    #
    @19
    hashf1lem2.2
    hashf1lem2.1
    cB
    cA
    mapfi
    syl2anc
    wph
    @1
    vf
    @18
    @1
    @0
    @18
    wcel
    wph
    cA
    cB
    @0
    wf
    cA
    cB
    @0
    f1f
    wph
    cB
    cA
    @0
    cfn
    cfn
    hashf1lem2.2
    hashf1lem2.1
    elmapd
    syl5ibr
    abssdv
    @18
    @2
    ssfi
    syl2anc
    wph
    vx
    cv
    #
    @2
    wss
    #
    @0
    cA
    cres
    #
    @22
    wcel
    #
    @7
    wa
    #
    vf
    cab
    #
    chash
    cfv
    #
    @12
    @22
    chash
    cfv
    #
    cmul
    co
    #
    wceq
    #
    wi
    #
    wi
    wph
    c0
    @2
    wss
    #
    cc0
    @12
    cc0
    cmul
    co
    #
    wceq
    #
    wi
    #
    wi
    wph
    vy
    cv
    #
    @2
    wss
    #
    @24
    @37
    wcel
    #
    @7
    wa
    #
    vf
    cab
    #
    chash
    cfv
    #
    @12
    @37
    chash
    cfv
    #
    cmul
    co
    #
    wceq
    #
    wi
    #
    wi
    wph
    @37
    va
    cv
    #
    csn
    #
    cun
    #
    @2
    wss
    #
    @24
    @49
    wcel
    #
    @7
    wa
    #
    vf
    cab
    #
    chash
    cfv
    #
    @12
    @49
    chash
    cfv
    #
    cmul
    co
    #
    wceq
    #
    wi
    #
    wi
    wph
    @17
    wi
    vx
    vy
    va
    @2
    @22
    c0
    wceq
    #
    @32
    @36
    wph
    @59
    @23
    @33
    @31
    @35
    @22
    c0
    @2
    sseq1
    @59
    @28
    cc0
    @30
    @34
    @59
    @28
    c0
    chash
    cfv
    #
    cc0
    @59
    @27
    c0
    chash
    @59
    @27
    c0
    wss
    @27
    c0
    wceq
    @59
    @26
    vf
    c0
    @59
    @25
    @0
    c0
    wcel
    #
    @7
    @59
    @25
    @24
    c0
    wcel
    #
    @61
    @22
    c0
    @24
    eleq2
    @62
    @61
    @24
    noel
    pm2.21i
    syl6bi
    adantrd
    abssdv
    @27
    ss0
    syl
    fveq2d
    hash0
    syl6eq
    @59
    @29
    cc0
    @12
    cmul
    @59
    @29
    @60
    cc0
    @22
    c0
    chash
    fveq2
    hash0
    syl6eq
    oveq2d
    eqeq12d
    imbi12d
    imbi2d
    @22
    @37
    wceq
    #
    @32
    @46
    wph
    @63
    @23
    @38
    @31
    @45
    @22
    @37
    @2
    sseq1
    @63
    @28
    @42
    @30
    @44
    @63
    @27
    @41
    chash
    @63
    @26
    @40
    vf
    @63
    @25
    @39
    @7
    @22
    @37
    @24
    eleq2
    anbi1d
    abbidv
    fveq2d
    @63
    @29
    @43
    @12
    cmul
    @22
    @37
    chash
    fveq2
    oveq2d
    eqeq12d
    imbi12d
    imbi2d
    @22
    @49
    wceq
    #
    @32
    @58
    wph
    @64
    @23
    @50
    @31
    @57
    @22
    @49
    @2
    sseq1
    @64
    @28
    @54
    @30
    @56
    @64
    @27
    @53
    chash
    @64
    @26
    @52
    vf
    @64
    @25
    @51
    @7
    @22
    @49
    @24
    eleq2
    anbi1d
    abbidv
    fveq2d
    @64
    @29
    @55
    @12
    cmul
    @22
    @49
    chash
    fveq2
    oveq2d
    eqeq12d
    imbi12d
    imbi2d
    @22
    @2
    wceq
    #
    @32
    @17
    wph
    @65
    @23
    @3
    @31
    @15
    @22
    @2
    @2
    sseq1
    @65
    @28
    @9
    @30
    @14
    @65
    @27
    @8
    chash
    @65
    @22
    cA
    cB
    @37
    wf1
    #
    vy
    cab
    #
    wceq
    #
    @27
    @8
    wceq
    @2
    @67
    @22
    @1
    @66
    vf
    vy
    cA
    cB
    @0
    @37
    f1eq1
    cbvabv
    eqeq2i
    @68
    @26
    @7
    vf
    @68
    @7
    @26
    @68
    @7
    @25
    @7
    @25
    @68
    @24
    @67
    wcel
    #
    @7
    cA
    cB
    @24
    wf1
    #
    @69
    @7
    cA
    @6
    wss
    @70
    cA
    @5
    ssun1
    @6
    cB
    cA
    @0
    f1ssres
    mpan2
    @66
    @70
    vy
    @24
    @0
    cA
    vf
    vex
    resex
    #
    cA
    cB
    @37
    @24
    f1eq1
    elab
    sylibr
    @22
    @67
    @24
    eleq2
    syl5ibr
    pm4.71rd
    bicomd
    abbidv
    sylbi
    fveq2d
    @65
    @29
    @13
    @12
    cmul
    @22
    @2
    chash
    fveq2
    oveq2d
    eqeq12d
    imbi12d
    imbi2d
    wph
    @35
    @33
    wph
    @34
    cc0
    wph
    @12
    wph
    @10
    @11
    wph
    @10
    wph
    @20
    @10
    cn0
    wcel
    hashf1lem2.2
    cB
    hashcl
    syl
    nn0cnd
    wph
    @11
    wph
    @21
    @11
    cn0
    wcel
    hashf1lem2.1
    cA
    hashcl
    syl
    nn0cnd
    #
    subcld
    #
    mul01d
    eqcomd
    a1d
    @37
    cfn
    wcel
    #
    @47
    @37
    wcel
    #
    wn
    #
    wa
    #
    wph
    @46
    @58
    wph
    @77
    @46
    @58
    wi
    @46
    @50
    @45
    wi
    wph
    @77
    wa
    #
    @58
    @50
    @38
    @45
    @37
    @49
    wss
    @50
    @38
    @37
    @48
    ssun1
    @37
    @49
    @2
    sstr
    mpan
    imim1i
    @78
    @50
    @45
    @57
    wph
    @77
    @50
    @45
    @57
    wi
    @45
    @57
    wph
    @77
    @50
    wa
    #
    wa
    #
    @42
    @12
    caddc
    co
    #
    @44
    @12
    caddc
    co
    #
    wceq
    @42
    @44
    @12
    caddc
    oveq1
    @80
    @54
    @81
    @56
    @82
    @80
    @54
    @42
    @24
    @47
    wceq
    #
    @7
    wa
    #
    vf
    cab
    #
    chash
    cfv
    #
    caddc
    co
    #
    @81
    @80
    @54
    @41
    @85
    cun
    #
    chash
    cfv
    #
    @87
    @53
    @88
    chash
    @53
    @40
    @84
    wo
    #
    vf
    cab
    @88
    @52
    @90
    vf
    @52
    @39
    @83
    wo
    #
    @7
    wa
    @90
    @51
    @91
    @7
    @51
    @39
    @24
    @48
    wcel
    #
    wo
    @91
    @24
    @37
    @48
    elun
    @92
    @83
    @39
    @24
    @47
    @71
    elsn
    orbi2i
    bitri
    anbi1i
    @39
    @83
    @7
    andir
    bitri
    abbii
    @40
    @84
    vf
    unab
    eqtr4i
    fveq2i
    @80
    @41
    cfn
    wcel
    #
    @85
    cfn
    wcel
    #
    @41
    @85
    cin
    #
    c0
    wceq
    @89
    @87
    wceq
    wph
    @93
    @79
    wph
    @6
    cB
    @0
    wf
    #
    vf
    cab
    #
    cfn
    wcel
    #
    @41
    @97
    wss
    @93
    wph
    cB
    @6
    cmap
    co
    #
    @97
    cfn
    wph
    @20
    @6
    cfn
    wcel
    #
    @99
    @97
    wceq
    hashf1lem2.2
    wph
    @21
    @5
    cfn
    wcel
    @100
    hashf1lem2.1
    @4
    snfi
    cA
    @5
    unfi
    sylancl
    #
    cB
    @6
    cfn
    cfn
    vf
    mapvalg
    syl2anc
    wph
    @20
    @100
    @99
    cfn
    wcel
    hashf1lem2.2
    @101
    cB
    @6
    mapfi
    syl2anc
    eqeltrrd
    #
    @40
    @96
    vf
    @7
    @96
    @39
    @6
    cB
    @0
    f1f
    #
    adantl
    ss2abi
    @97
    @41
    ssfi
    sylancl
    adantr
    wph
    @94
    @79
    wph
    @98
    @85
    @97
    wss
    @94
    @102
    @84
    @96
    vf
    @7
    @96
    @83
    @103
    adantl
    ss2abi
    @97
    @85
    ssfi
    sylancl
    #
    adantr
    @80
    @95
    @40
    @84
    wa
    #
    vf
    cab
    #
    c0
    @40
    @84
    vf
    inab
    @80
    @76
    @106
    c0
    wceq
    wph
    @74
    @76
    @50
    simprlr
    @75
    @106
    c0
    @106
    c0
    wne
    @105
    vf
    wex
    @75
    @105
    vf
    abn0
    @105
    @75
    vf
    @105
    @24
    @47
    @37
    @40
    @83
    @7
    simprl
    @39
    @7
    @84
    simpll
    eqeltrrd
    exlimiv
    sylbi
    necon1bi
    syl
    syl5eq
    @41
    @85
    hashun
    syl3anc
    syl5eq
    @80
    @86
    @12
    @42
    caddc
    @79
    wph
    cA
    cB
    @47
    wf1
    #
    @86
    @12
    wceq
    @79
    @47
    @2
    wcel
    #
    @107
    @79
    @48
    @2
    wss
    @108
    @79
    @37
    @48
    @2
    @77
    @50
    simpr
    unssbd
    @47
    @2
    va
    vex
    #
    snss
    sylibr
    @1
    @107
    vf
    @47
    @109
    cA
    cB
    @0
    @47
    f1eq1
    elab
    sylib
    wph
    @107
    wa
    #
    @11
    @86
    caddc
    co
    #
    @11
    cmin
    co
    @86
    @12
    @110
    @11
    @86
    wph
    @11
    cc
    wcel
    @107
    @72
    adantr
    @110
    @86
    @110
    @94
    @86
    cn0
    wcel
    wph
    @94
    @107
    @104
    adantr
    @85
    hashcl
    syl
    nn0cnd
    pncan2d
    @110
    @111
    @10
    @11
    cmin
    @110
    @111
    @47
    crn
    #
    chash
    cfv
    #
    cB
    @112
    cdif
    #
    chash
    cfv
    #
    caddc
    co
    #
    @112
    @114
    cun
    #
    chash
    cfv
    #
    @10
    @110
    @11
    @113
    @86
    @115
    caddc
    @110
    cA
    @112
    cen
    wbr
    #
    @11
    @113
    wceq
    @110
    @47
    cvv
    wcel
    #
    cA
    @112
    @47
    wf1o
    #
    @119
    @109
    @107
    @121
    wph
    cA
    cB
    @47
    f1f1orn
    adantl
    cA
    @112
    @47
    cvv
    f1oen3g
    sylancr
    cA
    @112
    hasheni
    syl
    @110
    @85
    @114
    cen
    wbr
    @86
    @115
    wceq
    @110
    vz
    cA
    cB
    vf
    @47
    wph
    @21
    @107
    hashf1lem2.1
    adantr
    wph
    @20
    @107
    hashf1lem2.2
    adantr
    #
    wph
    @4
    cA
    wcel
    wn
    @107
    hashf1lem2.3
    adantr
    wph
    @11
    c1
    caddc
    co
    @10
    cle
    wbr
    @107
    hashf1lem2.4
    adantr
    wph
    @107
    simpr
    hashf1lem1
    @85
    @114
    hasheni
    syl
    oveq12d
    @110
    @112
    cfn
    wcel
    #
    @114
    cfn
    wcel
    #
    @112
    @114
    cin
    c0
    wceq
    #
    @118
    @116
    wceq
    @110
    @20
    @112
    cB
    wss
    #
    @123
    @122
    @107
    @126
    wph
    @107
    cA
    cB
    @47
    wf
    @126
    cA
    cB
    @47
    f1f
    cA
    cB
    @47
    frn
    syl
    adantl
    #
    cB
    @112
    ssfi
    syl2anc
    @110
    @20
    @124
    @122
    cB
    @112
    diffi
    syl
    @125
    @110
    @112
    cB
    disjdif
    a1i
    @112
    @114
    hashun
    syl3anc
    @110
    @117
    cB
    chash
    @110
    @126
    @117
    cB
    wceq
    @127
    @112
    cB
    undif
    sylib
    fveq2d
    3eqtr2d
    oveq1d
    eqtr3d
    sylan2
    oveq2d
    eqtrd
    @80
    @56
    @12
    @43
    c1
    caddc
    co
    #
    cmul
    co
    @44
    @12
    c1
    cmul
    co
    #
    caddc
    co
    @82
    @80
    @55
    @128
    @12
    cmul
    @77
    @55
    @128
    wceq
    #
    wph
    @50
    @120
    @77
    @130
    wi
    @109
    @37
    @47
    cvv
    hashunsng
    ax-mp
    ad2antrl
    oveq2d
    @80
    @12
    @43
    c1
    wph
    @12
    cc
    wcel
    @79
    @73
    adantr
    #
    @80
    @43
    @80
    @74
    @43
    cn0
    wcel
    wph
    @74
    @76
    @50
    simprll
    @37
    hashcl
    syl
    nn0cnd
    @80
    1cnd
    adddid
    @80
    @129
    @12
    @44
    caddc
    @80
    @12
    @131
    mulid1d
    oveq2d
    3eqtrd
    eqeq12d
    syl5ibr
    expr
    a2d
    syl5
    expcom
    a2d
    findcard2s
    mpcom
    mpi
end
