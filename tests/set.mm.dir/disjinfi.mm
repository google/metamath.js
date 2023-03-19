include "cmpt.mm"
include "crn.mm"
include "cuni.mm"
include "cin.mm"
include "cfn.mm"
include "wcel.mm"
include "c0.mm"
include "wne.mm"
include "crab.mm"
include "cdom.mm"
include "wbr.mm"
include "wss.mm"
include "id.mm"
include "inss2.mm"
include "a1i.mm"
include "ssfi.mm"
include "syl2anc.mm"
include "syl.mm"
include "cvv.mm"
include "cv.mm"
include "crio.mm"
include "wfo.mm"
include "wa.mm"
include "jca.mm"
include "ssexg.mm"
include "wral.mm"
include "wceq.mm"
include "wrex.mm"
include "wreu.mm"
include "wsb.mm"
include "wi.mm"
include "elinel1.mm"
include "eluni2.mm"
include "biimpi.mm"
include "wb.mm"
include "vex.mm"
include "eqid.mm"
include "elrnmpt.mm"
include "ax-mp.mm"
include "adantr.mm"
include "nfcv.mm"
include "nfmpt1.mm"
include "nfrn.mm"
include "nfel.mm"
include "nfv.mm"
include "nfan.mm"
include "simpl.mm"
include "simpr.mm"
include "eleqtrd.mm"
include "ex.mm"
include "a1d.mm"
include "adantl.mm"
include "reximdai.mm"
include "mpd.mm"
include "rexlimdv.mm"
include "nfuni.mm"
include "nfin.mm"
include "nfre1.mm"
include "sseli.mm"
include "w3a.mm"
include "simp2.mm"
include "elind.mm"
include "3adant2.mm"
include "rspe.mm"
include "3exp.mm"
include "rexlimd.mm"
include "csb.mm"
include "wo.mm"
include "wn.mm"
include "wdisj.mm"
include "disjors.mm"
include "sylib.mm"
include "nfcsb1v.mm"
include "nfcsb1.mm"
include "nfeq.mm"
include "nfor.mm"
include "nfral.mm"
include "equequ1.mm"
include "csbeq1a.mm"
include "ineq1d.mm"
include "eqeq1d.mm"
include "orbi12d.mm"
include "ralbidv.mm"
include "cbvral.mm"
include "sylibr.mm"
include "rspa.mm"
include "sylan.mm"
include "orcomd.mm"
include "wsbc.mm"
include "sbsbc.mm"
include "sbcel2.mm"
include "csbin.mm"
include "eleq2i.mm"
include "3bitri.mm"
include "inelcm.mm"
include "neneqd.mm"
include "pm2.53.mm"
include "sylc.mm"
include "ralrimiva.mm"
include "reu2.mm"
include "riotacl2.mm"
include "nfriota1.mm"
include "eleq2d.mm"
include "elrabf.mm"
include "simpld.mm"
include "simprd.mm"
include "ne0i.mm"
include "nfne.mm"
include "neeq1d.mm"
include "wex.mm"
include "simprbi.mm"
include "n0.mm"
include "simplbi.mm"
include "simplr.mm"
include "nfim.mm"
include "eleq1.mm"
include "anbi2d.mm"
include "eleq1d.mm"
include "imbi12d.mm"
include "chvar.mm"
include "elrnmpt1.mm"
include "equcoms.mm"
include "eqcomd.mm"
include "cbvmpt.mm"
include "rneqi.mm"
include "syl6eleq.mm"
include "elunii.mm"
include "elinel2.mm"
include "cbvriota.mm"
include "adantll.mm"
include "simpll.mm"
include "sbequ.mm"
include "csbconstg.mm"
include "ineq2i.mm"
include "eqtri.mm"
include "bitri.mm"
include "3bitrd.mm"
include "equequ2.mm"
include "cbvralv.mm"
include "ralbii.mm"
include "anbi1d.mm"
include "biid.mm"
include "csbco.mm"
include "ineq12i.mm"
include "3eqtri.mm"
include "3bitrri.mm"
include "anbi2i.mm"
include "imbi1i.mm"
include "riota1.mm"
include "mpbid.mm"
include "eqtr2d.mm"
include "eximd.mm"
include "df-rex.mm"
include "fompt.mm"
include "fodomg.mm"
include "domfi.mm"

theorem disjinfi
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cC: class C
  let cV: class V
  let vw: setvar w
  let vy: setvar y
  let vz: setvar z
  assume disjinfi.b: |- ( ( ph /\ x e. A ) -> B e. V )
  assume disjinfi.d: |- ( ph -> Disj_ x e. A B )
  assume disjinfi.c: |- ( ph -> C e. Fin )

  disjoint A x
  disjoint C x
  disjoint V x
  disjoint ph x
  disjoint A w
  disjoint A y
  disjoint A z
  disjoint w x
  disjoint w y
  disjoint w z
  disjoint x y
  disjoint x z
  disjoint y z
  disjoint B w
  disjoint B y
  disjoint B z
  disjoint C w
  disjoint C y
  disjoint C z
  disjoint ph w
  disjoint ph y
  assert |- ( ph -> { x e. A | ( B i^i C ) =/= (/) } e. Fin )

  proof
    wph
    vx
    cA
    cB
    cmpt
    #
    crn
    #
    cuni
    #
    cC
    cin
    #
    cfn
    wcel
    #
    cB
    cC
    cin
    #
    c0
    wne
    #
    vx
    cA
    crab
    #
    @3
    cdom
    wbr
    #
    @7
    cfn
    wcel
    wph
    cC
    cfn
    wcel
    #
    @4
    disjinfi.c
    @9
    @9
    @3
    cC
    wss
    #
    @4
    @9
    id
    @10
    @9
    @2
    cC
    inss2
    #
    a1i
    cC
    @3
    ssfi
    syl2anc
    syl
    wph
    @3
    cvv
    wcel
    #
    @3
    @7
    vy
    @3
    vy
    cv
    #
    @5
    wcel
    #
    vx
    cA
    crio
    #
    cmpt
    #
    wfo
    #
    @8
    wph
    @10
    @9
    wa
    @12
    wph
    @10
    @9
    @10
    wph
    @11
    a1i
    disjinfi.c
    jca
    @3
    cC
    cfn
    ssexg
    syl
    wph
    @15
    @7
    wcel
    #
    vy
    @3
    wral
    #
    vw
    cv
    #
    @15
    wceq
    #
    vy
    @3
    wrex
    #
    vw
    @7
    wral
    #
    wa
    @17
    wph
    @19
    @23
    wph
    @18
    vy
    @3
    wph
    @13
    @3
    wcel
    #
    wa
    #
    @15
    @14
    vx
    cA
    crab
    wcel
    #
    @18
    @25
    @14
    vx
    cA
    wreu
    #
    @26
    @25
    @14
    vx
    cA
    wrex
    #
    @14
    @14
    vx
    vw
    wsb
    #
    wa
    #
    vx
    cv
    #
    @20
    wceq
    #
    wi
    #
    vw
    cA
    wral
    #
    vx
    cA
    wral
    #
    wa
    @27
    @25
    @28
    @35
    @25
    @13
    cB
    wcel
    #
    vx
    cA
    wrex
    #
    @28
    @24
    @37
    wph
    @24
    @13
    @2
    wcel
    #
    @37
    @13
    @2
    cC
    elinel1
    @38
    @13
    @20
    wcel
    #
    vw
    @1
    wrex
    #
    @37
    @38
    @40
    vw
    @13
    @1
    eluni2
    biimpi
    @38
    @39
    @37
    vw
    @1
    @20
    @1
    wcel
    #
    @39
    @37
    wi
    wi
    @38
    @41
    @39
    @37
    @41
    @39
    wa
    #
    @20
    cB
    wceq
    #
    vx
    cA
    wrex
    #
    @37
    @41
    @44
    @39
    @41
    @44
    @20
    cvv
    wcel
    @41
    @44
    wb
    vw
    vex
    vx
    cA
    cB
    @20
    @0
    cvv
    @0
    eqid
    elrnmpt
    ax-mp
    biimpi
    adantr
    @42
    @43
    @36
    vx
    cA
    @41
    @39
    vx
    vx
    @20
    @1
    vx
    @20
    nfcv
    #
    vx
    @0
    vx
    cA
    cB
    nfmpt1
    nfrn
    #
    nfel
    @39
    vx
    nfv
    nfan
    @39
    @31
    cA
    wcel
    #
    @43
    @36
    wi
    #
    wi
    @41
    @39
    @48
    @47
    @39
    @43
    @36
    @39
    @43
    wa
    @13
    @20
    cB
    @39
    @43
    simpl
    @39
    @43
    simpr
    eleqtrd
    ex
    a1d
    adantl
    reximdai
    mpd
    ex
    a1i
    rexlimdv
    mpd
    syl
    adantl
    @25
    @36
    @28
    vx
    cA
    wph
    @24
    vx
    wph
    vx
    nfv
    vx
    @13
    @3
    vx
    @13
    nfcv
    #
    vx
    @2
    cC
    vx
    @1
    @46
    nfuni
    vx
    cC
    nfcv
    #
    nfin
    nfel
    nfan
    @14
    vx
    cA
    nfre1
    @24
    @47
    @36
    @28
    wi
    wi
    #
    wph
    @24
    @13
    cC
    wcel
    #
    @51
    @3
    cC
    @13
    @11
    sseli
    @52
    @47
    @36
    @28
    @52
    @47
    @36
    w3a
    @47
    @14
    @28
    @52
    @47
    @36
    simp2
    @52
    @36
    @14
    @47
    @52
    @36
    wa
    cB
    cC
    @13
    @52
    @36
    simpr
    @52
    @36
    simpl
    elind
    3adant2
    @14
    vx
    cA
    rspe
    syl2anc
    3exp
    syl
    adantl
    rexlimd
    mpd
    wph
    @35
    @24
    wph
    @34
    vx
    cA
    wph
    @47
    wa
    #
    @33
    vw
    cA
    @53
    @20
    cA
    wcel
    #
    wa
    #
    @30
    @32
    @55
    @30
    wa
    cB
    vx
    @20
    cB
    csb
    #
    cin
    #
    c0
    wceq
    #
    @32
    wo
    #
    @58
    wn
    #
    @32
    @55
    @59
    @30
    @55
    @32
    @58
    wo
    #
    vw
    cA
    wral
    #
    @54
    @59
    @53
    @62
    @54
    wph
    @62
    vx
    cA
    wral
    #
    @47
    @62
    wph
    vz
    cv
    #
    @20
    wceq
    #
    vx
    @64
    cB
    csb
    #
    @56
    cin
    #
    c0
    wceq
    #
    wo
    #
    vw
    cA
    wral
    #
    vz
    cA
    wral
    #
    @63
    wph
    vx
    cA
    cB
    wdisj
    @71
    disjinfi.d
    vx
    cA
    cB
    vz
    vw
    disjors
    sylib
    @62
    @70
    vx
    vz
    cA
    @62
    vz
    nfv
    @69
    vx
    vw
    cA
    vx
    cA
    nfcv
    #
    @65
    @68
    vx
    @65
    vx
    nfv
    vx
    @67
    c0
    vx
    @66
    @56
    vx
    @64
    cB
    nfcsb1v
    #
    vx
    @20
    cB
    @45
    nfcsb1
    #
    nfin
    vx
    c0
    nfcv
    #
    nfeq
    nfor
    nfral
    @31
    @64
    wceq
    #
    @61
    @69
    vw
    cA
    @76
    @32
    @65
    @58
    @68
    vx
    vz
    vw
    equequ1
    @76
    @57
    @67
    c0
    @76
    cB
    @66
    @56
    vx
    @64
    cB
    csbeq1a
    ineq1d
    eqeq1d
    orbi12d
    ralbidv
    cbvral
    sylibr
    @62
    vx
    cA
    rspa
    sylan
    adantr
    @53
    @54
    simpr
    @62
    @54
    wa
    @32
    @58
    @61
    vw
    cA
    rspa
    orcomd
    syl2anc
    adantr
    @30
    @60
    @55
    @30
    @36
    @13
    @56
    wcel
    #
    wa
    #
    @60
    @30
    @36
    @77
    @14
    @36
    @29
    @13
    cB
    cC
    elinel1
    adantr
    @29
    @77
    @14
    @29
    @13
    @56
    vx
    @20
    cC
    csb
    #
    cin
    #
    wcel
    #
    @77
    @29
    @81
    @29
    @14
    vx
    @20
    wsbc
    @13
    vx
    @20
    @5
    csb
    #
    wcel
    @81
    @14
    vx
    vw
    sbsbc
    vx
    @20
    @13
    @5
    sbcel2
    @82
    @80
    @13
    vx
    @20
    cB
    cC
    csbin
    eleq2i
    3bitri
    biimpi
    @13
    @56
    @79
    elinel1
    syl
    adantl
    jca
    @78
    @57
    c0
    @13
    cB
    @56
    inelcm
    neneqd
    syl
    adantl
    @58
    @32
    pm2.53
    sylc
    ex
    ralrimiva
    ralrimiva
    adantr
    #
    jca
    @14
    vx
    vw
    cA
    reu2
    sylibr
    @14
    vx
    cA
    riotacl2
    syl
    @26
    @15
    cA
    wcel
    #
    vx
    @15
    cB
    csb
    #
    cC
    cin
    #
    c0
    wne
    #
    wa
    @18
    @26
    @84
    @87
    @26
    @84
    @13
    @86
    wcel
    #
    @26
    @84
    @88
    wa
    @14
    @88
    vx
    @15
    cA
    @14
    vx
    cA
    nfriota1
    #
    @72
    vx
    @13
    @86
    @49
    vx
    @85
    cC
    vx
    @15
    cB
    @89
    nfcsb1
    @50
    nfin
    #
    nfel
    @31
    @15
    wceq
    #
    @5
    @86
    @13
    @91
    cB
    @85
    cC
    vx
    @15
    cB
    csbeq1a
    ineq1d
    #
    eleq2d
    elrabf
    biimpi
    #
    simpld
    @26
    @88
    @87
    @26
    @84
    @88
    @93
    simprd
    @86
    @13
    ne0i
    syl
    jca
    @6
    @87
    vx
    @15
    cA
    @89
    @72
    vx
    @86
    c0
    @90
    @75
    nfne
    @91
    @5
    @86
    c0
    @92
    neeq1d
    elrabf
    sylibr
    syl
    ralrimiva
    wph
    @22
    vw
    @7
    wph
    @20
    @7
    wcel
    #
    wa
    #
    @24
    @21
    wa
    #
    vy
    wex
    #
    @22
    @95
    @13
    @56
    cC
    cin
    #
    wcel
    #
    vy
    wex
    #
    @97
    @94
    @100
    wph
    @94
    @98
    c0
    wne
    #
    @100
    @94
    @54
    @101
    @6
    @101
    vx
    @20
    cA
    @45
    @72
    vx
    @98
    c0
    vx
    @56
    cC
    @74
    @50
    nfin
    #
    @75
    nfne
    @32
    @5
    @98
    c0
    @32
    cB
    @56
    cC
    vx
    @20
    cB
    csbeq1a
    #
    ineq1d
    #
    neeq1d
    elrabf
    #
    simprbi
    vy
    @98
    n0
    sylib
    adantl
    @95
    @99
    @96
    vy
    @95
    vy
    nfv
    @95
    wph
    @54
    @99
    @96
    wi
    wph
    @94
    simpl
    @94
    @54
    wph
    @94
    @54
    @101
    @105
    simplbi
    adantl
    wph
    @54
    wa
    #
    @99
    @96
    @106
    @99
    wa
    #
    @24
    @21
    @107
    @2
    cC
    @13
    @107
    @77
    @56
    @1
    wcel
    @38
    @99
    @77
    @106
    @13
    @56
    cC
    elinel1
    adantl
    @107
    @56
    vw
    cA
    @56
    cmpt
    #
    crn
    #
    @1
    @107
    @54
    @56
    cV
    wcel
    #
    @56
    @109
    wcel
    wph
    @54
    @99
    simplr
    #
    @106
    @110
    @99
    @53
    cB
    cV
    wcel
    #
    wi
    @106
    @110
    wi
    vx
    vw
    @106
    @110
    vx
    @106
    vx
    nfv
    vx
    @56
    cV
    @74
    vx
    cV
    nfcv
    nfel
    nfim
    @32
    @53
    @106
    @112
    @110
    @32
    @47
    @54
    wph
    @31
    @20
    cA
    eleq1
    anbi2d
    @32
    cB
    @56
    cV
    @103
    eleq1d
    imbi12d
    disjinfi.b
    chvar
    adantr
    vw
    cA
    @56
    @108
    cV
    @108
    eqid
    elrnmpt1
    syl2anc
    @108
    @0
    vw
    vx
    cA
    @56
    cB
    @74
    vw
    cB
    nfcv
    @20
    @31
    wceq
    cB
    @56
    cB
    @56
    wceq
    vx
    vw
    @103
    equcoms
    eqcomd
    cbvmpt
    rneqi
    syl6eleq
    @13
    @56
    @1
    elunii
    syl2anc
    @99
    @52
    @106
    @13
    @56
    cC
    elinel2
    adantl
    elind
    #
    @107
    @15
    @99
    vw
    cA
    crio
    #
    @20
    @15
    @114
    wceq
    @107
    @14
    @99
    vx
    vw
    cA
    @14
    vw
    nfv
    vx
    @13
    @98
    @49
    @102
    nfel
    #
    @32
    @5
    @98
    @13
    @104
    eleq2d
    #
    cbvriota
    a1i
    @107
    @54
    @99
    wa
    #
    @114
    @20
    wceq
    #
    @107
    @54
    @99
    @111
    @106
    @99
    simpr
    jca
    @107
    @99
    vw
    cA
    wreu
    #
    @117
    @118
    wb
    @107
    @99
    vw
    cA
    wrex
    #
    @99
    @99
    vw
    vz
    wsb
    #
    wa
    #
    @20
    @64
    wceq
    #
    wi
    #
    vz
    cA
    wral
    #
    vw
    cA
    wral
    #
    wa
    @119
    @107
    @120
    @126
    @54
    @99
    @120
    wph
    @99
    vw
    cA
    rspe
    adantll
    @107
    wph
    @24
    @126
    wph
    @54
    @99
    simpll
    @113
    @25
    @35
    @126
    @83
    @35
    @14
    @13
    @66
    cC
    cin
    #
    wcel
    #
    wa
    #
    @76
    wi
    #
    vz
    cA
    wral
    #
    vx
    cA
    wral
    @99
    @128
    wa
    #
    @123
    wi
    #
    vz
    cA
    wral
    #
    vw
    cA
    wral
    #
    @126
    @34
    @131
    vx
    cA
    @33
    @130
    vw
    vz
    cA
    @123
    @30
    @129
    @32
    @76
    @123
    @29
    @128
    @14
    @123
    @29
    @14
    vx
    vz
    wsb
    #
    @14
    vx
    @64
    wsbc
    #
    @128
    @14
    vw
    vz
    vx
    sbequ
    @136
    @137
    wb
    @123
    @14
    vx
    vz
    sbsbc
    a1i
    @137
    @128
    wb
    @123
    @137
    @13
    vx
    @64
    @5
    csb
    #
    wcel
    @128
    vx
    @64
    @13
    @5
    sbcel2
    @138
    @127
    @13
    @138
    @66
    vx
    @64
    cC
    csb
    #
    cin
    @127
    vx
    @64
    cB
    cC
    csbin
    @139
    cC
    @66
    @64
    cvv
    wcel
    #
    @139
    cC
    wceq
    vz
    vex
    #
    vx
    @64
    cC
    cvv
    csbconstg
    ax-mp
    ineq2i
    eqtri
    eleq2i
    bitri
    a1i
    3bitrd
    anbi2d
    vw
    vz
    vx
    equequ2
    imbi12d
    cbvralv
    ralbii
    @131
    @134
    vx
    vw
    cA
    @131
    vw
    nfv
    @133
    vx
    vz
    cA
    @72
    @132
    @123
    vx
    @99
    @128
    vx
    @115
    vx
    @13
    @127
    @49
    vx
    @66
    cC
    @73
    @50
    nfin
    nfel
    nfan
    @123
    vx
    nfv
    nfim
    nfral
    @32
    @130
    @133
    vz
    cA
    @32
    @129
    @132
    @76
    @123
    @32
    @14
    @99
    @128
    @116
    anbi1d
    vx
    vw
    vz
    equequ1
    imbi12d
    ralbidv
    cbvral
    @135
    @135
    @126
    @135
    biid
    @134
    @125
    vw
    cA
    @133
    @124
    vz
    cA
    @132
    @122
    @123
    @128
    @121
    @99
    @121
    @99
    vw
    @64
    wsbc
    @13
    vw
    @64
    @98
    csb
    #
    wcel
    @128
    @99
    vw
    vz
    sbsbc
    vw
    @64
    @13
    @98
    sbcel2
    @142
    @127
    @13
    @142
    vw
    @64
    @56
    csb
    #
    vw
    @64
    cC
    csb
    #
    cin
    @127
    @127
    vw
    @64
    @56
    cC
    csbin
    @143
    @66
    @144
    cC
    vx
    vw
    @64
    cB
    csbco
    @140
    @144
    cC
    wceq
    @141
    vw
    @64
    cC
    cvv
    csbconstg
    ax-mp
    ineq12i
    @127
    eqid
    3eqtri
    eleq2i
    3bitrri
    anbi2i
    imbi1i
    ralbii
    ralbii
    bitri
    3bitri
    sylib
    syl2anc
    jca
    @99
    vw
    vz
    cA
    reu2
    sylibr
    @99
    vw
    cA
    riota1
    syl
    mpbid
    eqtr2d
    jca
    ex
    syl2anc
    eximd
    mpd
    @21
    vy
    @3
    df-rex
    sylibr
    ralrimiva
    jca
    vy
    vw
    @3
    @7
    @15
    @16
    @16
    eqid
    fompt
    sylibr
    @3
    @7
    cvv
    @16
    fodomg
    sylc
    @3
    @7
    domfi
    syl2anc
end
