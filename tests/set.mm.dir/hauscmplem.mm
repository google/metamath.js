include "cv.mm"
include "cuni.mm"
include "wss.mm"
include "wcel.mm"
include "ccl.mm"
include "cfv.mm"
include "cdif.mm"
include "wa.mm"
include "wrex.mm"
include "cpw.mm"
include "cfn.mm"
include "cin.mm"
include "c0.mm"
include "wceq.mm"
include "ctop.mm"
include "cha.mm"
include "haustop.mm"
include "syl.mm"
include "ad3antrrr.mm"
include "topopn.mm"
include "eldifad.mm"
include "clstop.mm"
include "simplr.mm"
include "unieq.mm"
include "uni0.mm"
include "syl6eq.mm"
include "adantl.mm"
include "sseqtrd.mm"
include "ss0.mm"
include "difeq2d.mm"
include "dif0.mm"
include "eqtr4d.mm"
include "eqimss.mm"
include "eleq2.mm"
include "fveq2.mm"
include "sseq1d.mm"
include "anbi12d.mm"
include "rspcev.mm"
include "syl12anc.mm"
include "wne.mm"
include "wf.mm"
include "wral.mm"
include "wex.mm"
include "elin.mm"
include "id.mm"
include "elpwi.mm"
include "sseld.mm"
include "difeq2.mm"
include "sseq2d.mm"
include "anbi2d.mm"
include "rexbidv.mm"
include "elrab2.mm"
include "simprbi.mm"
include "syl6.mm"
include "ralrimiv.mm"
include "ac6sfi.mm"
include "syl2anr.mm"
include "sylbi.mm"
include "ad2antlr.mm"
include "crn.mm"
include "cint.mm"
include "frn.mm"
include "ad2antrl.mm"
include "simprr.mm"
include "simpl.mm"
include "cdm.mm"
include "dm0rn0.mm"
include "fdm.mm"
include "eqeq1d.mm"
include "syl5rbbr.mm"
include "necon3bid.mm"
include "biimpac.mm"
include "syl2an.mm"
include "wfo.mm"
include "wfn.mm"
include "ffn.mm"
include "dffn4.mm"
include "sylib.mm"
include "adantr.mm"
include "fofi.mm"
include "w3a.mm"
include "fiinopn.mm"
include "imp.mm"
include "syl13anc.mm"
include "ciin.mm"
include "ralimi.mm"
include "ad2antll.mm"
include "wb.mm"
include "eliin.mm"
include "mpbird.mm"
include "cab.mm"
include "fnrnfv.mm"
include "inteqd.mm"
include "fvex.mm"
include "dfiin2.mm"
include "syl6eqr.mm"
include "eleqtrrd.mm"
include "ccld.mm"
include "ad4antr.mm"
include "ffvelrn.mm"
include "adantll.mm"
include "elssuni.mm"
include "syl6sseqr.mm"
include "clscld.mm"
include "syl2anc.mm"
include "ralrimiva.mm"
include "adantrr.mm"
include "iincld.mm"
include "sscls.mm"
include "ssel.mm"
include "ral2imi.mm"
include "cvv.mm"
include "vex.mm"
include "ax-mp.mm"
include "3imtr4g.mm"
include "ssrdv.mm"
include "eqsstrd.mm"
include "clsss2.mm"
include "wi.mm"
include "ciun.mm"
include "iindif2.mm"
include "simplrl.mm"
include "uniiun.mm"
include "sseq2i.mm"
include "sscon.mm"
include "sstrd.mm"
include "exlimddv.mm"
include "anassrs.mm"
include "pm2.61dane.mm"
include "sselda.mm"
include "wn.mm"
include "eldifbd.mm"
include "nelne2.mm"
include "hausnei.mm"
include "3anass.mm"
include "incom.mm"
include "eqeq1i.mm"
include "reldisj.mm"
include "syl5bb.mm"
include "opncld.mm"
include "sylan.mm"
include "ex.mm"
include "sylbid.mm"
include "anim2d.mm"
include "syl5bi.mm"
include "reximdva.mm"
include "r19.42v.mm"
include "syl6ib.mm"
include "mpd.mm"
include "crab.mm"
include "unieqi.mm"
include "eleq2i.mm"
include "elunirab.mm"
include "bitri.mm"
include "sylibr.mm"
include "ssrab2.mm"
include "eqsstri.mm"
include "elpw2g.mm"
include "mpbiri.mm"
include "crest.mm"
include "co.mm"
include "ccmp.mm"
include "cmpsub.mm"
include "biimp3a.mm"
include "syl3anc.mm"
include "pweq.mm"
include "ineq1d.mm"
include "rexeqdv.mm"
include "imbi12d.mm"
include "rspcva.mm"
include "r19.29a.mm"

theorem hauscmplem
  let wph: wff ph
  let vy: setvar y
  let vz: setvar z
  let vw: setvar w
  let cA: class A
  let cS: class S
  let cJ: class J
  let cO: class O
  let cX: class X
  let vf: setvar f
  let vx: setvar x
  assume hauscmp.1: |- X = U. J
  assume hauscmplem.2: |- O = { y e. J | E. w e. J ( A e. w /\ ( ( cls ` J ) ` w ) C_ ( X \ y ) ) }
  assume hauscmplem.3: |- ( ph -> J e. Haus )
  assume hauscmplem.4: |- ( ph -> S C_ X )
  assume hauscmplem.5: |- ( ph -> ( J |`t S ) e. Comp )
  assume hauscmplem.6: |- ( ph -> A e. ( X \ S ) )

  disjoint w y
  disjoint w z
  disjoint A w
  disjoint y z
  disjoint A y
  disjoint A z
  disjoint J w
  disjoint J y
  disjoint J z
  disjoint ph w
  disjoint ph y
  disjoint ph z
  disjoint S w
  disjoint S y
  disjoint S z
  disjoint O z
  disjoint X w
  disjoint X y
  disjoint X z
  disjoint f w
  disjoint f x
  disjoint f y
  disjoint f z
  disjoint A f
  disjoint w x
  disjoint x y
  disjoint x z
  disjoint A x
  disjoint J f
  disjoint J x
  disjoint f ph
  disjoint ph x
  disjoint S f
  disjoint S x
  disjoint O f
  disjoint O x
  disjoint X f
  disjoint X x
  assert |- ( ph -> E. z e. J ( A e. z /\ ( ( cls ` J ) ` z ) C_ ( X \ S ) ) )

  proof
    wph
    cS
    vx
    cv
    #
    cuni
    #
    wss
    #
    cA
    vz
    cv
    #
    wcel
    #
    @3
    cJ
    ccl
    cfv
    #
    cfv
    #
    cX
    cS
    cdif
    #
    wss
    #
    wa
    #
    vz
    cJ
    wrex
    #
    vx
    cO
    cpw
    #
    cfn
    cin
    #
    wph
    @0
    @12
    wcel
    #
    wa
    #
    @2
    wa
    #
    @10
    @0
    c0
    @15
    @0
    c0
    wceq
    #
    wa
    #
    cX
    cJ
    wcel
    #
    cA
    cX
    wcel
    #
    cX
    @5
    cfv
    #
    @7
    wss
    #
    @10
    @17
    cJ
    ctop
    wcel
    #
    @18
    wph
    @22
    @13
    @2
    @16
    wph
    cJ
    cha
    wcel
    #
    @22
    hauscmplem.3
    cJ
    haustop
    #
    syl
    #
    ad3antrrr
    #
    cJ
    cX
    hauscmp.1
    topopn
    syl
    wph
    @19
    @13
    @2
    @16
    wph
    cA
    cX
    cS
    hauscmplem.6
    eldifad
    #
    ad3antrrr
    @17
    @20
    @7
    wceq
    @21
    @17
    @20
    cX
    @7
    @17
    @22
    @20
    cX
    wceq
    @26
    cJ
    cX
    hauscmp.1
    clstop
    syl
    @17
    @7
    cX
    c0
    cdif
    cX
    @17
    cS
    c0
    cX
    @17
    cS
    c0
    wss
    cS
    c0
    wceq
    @17
    cS
    @1
    c0
    @14
    @2
    @16
    simplr
    @16
    @1
    c0
    wceq
    @15
    @16
    @1
    c0
    cuni
    c0
    @0
    c0
    unieq
    uni0
    syl6eq
    adantl
    sseqtrd
    cS
    ss0
    syl
    difeq2d
    cX
    dif0
    syl6eq
    eqtr4d
    @20
    @7
    eqimss
    syl
    @9
    @19
    @21
    wa
    vz
    cX
    cJ
    @3
    cX
    wceq
    #
    @4
    @19
    @8
    @21
    @3
    cX
    cA
    eleq2
    @28
    @6
    @20
    @7
    @3
    cX
    @5
    fveq2
    sseq1d
    anbi12d
    rspcev
    syl12anc
    @14
    @2
    @0
    c0
    wne
    #
    @10
    @14
    @2
    @29
    wa
    #
    wa
    #
    @0
    cJ
    vf
    cv
    #
    wf
    #
    cA
    @3
    @32
    cfv
    #
    wcel
    #
    @34
    @5
    cfv
    #
    cX
    @3
    cdif
    #
    wss
    #
    wa
    #
    vz
    @0
    wral
    #
    wa
    #
    @10
    vf
    @13
    @41
    vf
    wex
    #
    wph
    @30
    @13
    @0
    @11
    wcel
    #
    @0
    cfn
    wcel
    #
    wa
    @42
    @0
    @11
    cfn
    elin
    #
    @44
    @44
    cA
    vw
    cv
    #
    wcel
    #
    @46
    @5
    cfv
    #
    @37
    wss
    #
    wa
    #
    vw
    cJ
    wrex
    #
    vz
    @0
    wral
    @42
    @43
    @44
    id
    @43
    @51
    vz
    @0
    @43
    @3
    @0
    wcel
    #
    @3
    cO
    wcel
    #
    @51
    @43
    @0
    cO
    @3
    @0
    cO
    elpwi
    sseld
    @53
    @3
    cJ
    wcel
    @51
    @47
    @48
    cX
    vy
    cv
    #
    cdif
    #
    wss
    #
    wa
    #
    vw
    cJ
    wrex
    #
    @51
    vy
    @3
    cJ
    cO
    @54
    @3
    wceq
    #
    @57
    @50
    vw
    cJ
    @59
    @56
    @49
    @47
    @59
    @55
    @37
    @48
    @54
    @3
    cX
    difeq2
    sseq2d
    anbi2d
    rexbidv
    hauscmplem.2
    elrab2
    simprbi
    syl6
    ralrimiv
    @50
    @39
    vz
    vw
    @0
    cJ
    vf
    @46
    @34
    wceq
    #
    @47
    @35
    @49
    @38
    @46
    @34
    cA
    eleq2
    @60
    @48
    @36
    @37
    @46
    @34
    @5
    fveq2
    sseq1d
    anbi12d
    ac6sfi
    syl2anr
    sylbi
    ad2antlr
    @31
    @41
    wa
    #
    @32
    crn
    #
    cint
    #
    cJ
    wcel
    #
    cA
    @63
    wcel
    #
    @63
    @5
    cfv
    #
    @7
    wss
    #
    @10
    @61
    @22
    @62
    cJ
    wss
    #
    @62
    c0
    wne
    #
    @62
    cfn
    wcel
    #
    @64
    wph
    @22
    @13
    @30
    @41
    @25
    ad3antrrr
    @33
    @68
    @31
    @40
    @0
    cJ
    @32
    frn
    ad2antrl
    @31
    @29
    @33
    @69
    @41
    @14
    @2
    @29
    simprr
    #
    @33
    @40
    simpl
    @33
    @29
    @69
    @33
    @0
    c0
    @62
    c0
    @62
    c0
    wceq
    @32
    cdm
    #
    c0
    wceq
    @33
    @16
    @32
    dm0rn0
    @33
    @72
    @0
    c0
    @0
    cJ
    @32
    fdm
    eqeq1d
    syl5rbbr
    necon3bid
    biimpac
    syl2an
    @31
    @44
    @0
    @62
    @32
    wfo
    #
    @70
    @41
    @13
    @44
    wph
    @30
    @13
    @43
    @44
    @45
    simprbi
    ad2antlr
    @33
    @73
    @40
    @33
    @32
    @0
    wfn
    #
    @73
    @0
    cJ
    @32
    ffn
    #
    @0
    @32
    dffn4
    sylib
    adantr
    @0
    @62
    @32
    fofi
    syl2an
    @22
    @68
    @69
    @70
    w3a
    @64
    @62
    cJ
    fiinopn
    imp
    syl13anc
    @61
    cA
    vz
    @0
    @34
    ciin
    #
    @63
    @61
    cA
    @76
    wcel
    #
    @35
    vz
    @0
    wral
    #
    @40
    @78
    @31
    @33
    @39
    @35
    vz
    @0
    @35
    @38
    simpl
    ralimi
    ad2antll
    @61
    cA
    @7
    wcel
    #
    @77
    @78
    wb
    wph
    @79
    @13
    @30
    @41
    hauscmplem.6
    ad3antrrr
    vz
    cA
    @0
    @34
    @7
    eliin
    syl
    mpbird
    @61
    @74
    @63
    @76
    wceq
    @33
    @74
    @31
    @40
    @75
    ad2antrl
    @74
    @63
    @54
    @34
    wceq
    vz
    @0
    wrex
    vy
    cab
    #
    cint
    @76
    @74
    @62
    @80
    vz
    vy
    @0
    @32
    fnrnfv
    inteqd
    vz
    vy
    @0
    @34
    @3
    @32
    fvex
    dfiin2
    syl6eqr
    syl
    #
    eleqtrrd
    @61
    @66
    vz
    @0
    @36
    ciin
    #
    @7
    @61
    @82
    cJ
    ccld
    cfv
    #
    wcel
    #
    @63
    @82
    wss
    @66
    @82
    wss
    @61
    @29
    @36
    @83
    wcel
    #
    vz
    @0
    wral
    #
    @84
    @31
    @29
    @41
    @71
    adantr
    #
    @31
    @33
    @86
    @40
    @31
    @33
    wa
    #
    @85
    vz
    @0
    @88
    @52
    wa
    #
    @22
    @34
    cX
    wss
    #
    @85
    wph
    @22
    @13
    @30
    @33
    @52
    @25
    ad4antr
    #
    @89
    @34
    cJ
    cuni
    #
    cX
    @89
    @34
    cJ
    wcel
    #
    @34
    @92
    wss
    @33
    @52
    @93
    @31
    @0
    cJ
    @3
    @32
    ffvelrn
    adantll
    @34
    cJ
    elssuni
    syl
    hauscmp.1
    syl6sseqr
    #
    @34
    cJ
    cX
    hauscmp.1
    clscld
    syl2anc
    ralrimiva
    adantrr
    vz
    @0
    @36
    cJ
    iincld
    syl2anc
    @61
    @63
    @76
    @82
    @81
    @31
    @33
    @76
    @82
    wss
    #
    @40
    @88
    @34
    @36
    wss
    #
    vz
    @0
    wral
    #
    @95
    @88
    @96
    vz
    @0
    @89
    @22
    @90
    @96
    @91
    @94
    @34
    cJ
    cX
    hauscmp.1
    sscls
    syl2anc
    ralrimiva
    @97
    vy
    @76
    @82
    @97
    @54
    @34
    wcel
    #
    vz
    @0
    wral
    #
    @54
    @36
    wcel
    #
    vz
    @0
    wral
    #
    @54
    @76
    wcel
    #
    @54
    @82
    wcel
    #
    @96
    @98
    @100
    vz
    @0
    @34
    @36
    @54
    ssel
    ral2imi
    @54
    cvv
    wcel
    #
    @102
    @99
    wb
    vy
    vex
    #
    vz
    @54
    @0
    @34
    cvv
    eliin
    ax-mp
    @104
    @103
    @101
    wb
    @105
    vz
    @54
    @0
    @36
    cvv
    eliin
    ax-mp
    #
    3imtr4g
    ssrdv
    syl
    adantrr
    eqsstrd
    @82
    @63
    cJ
    cX
    hauscmp.1
    clsss2
    syl2anc
    @61
    @82
    vz
    @0
    @37
    ciin
    #
    @7
    @40
    @82
    @107
    wss
    @31
    @33
    @40
    vy
    @82
    @107
    @40
    @101
    @54
    @37
    wcel
    #
    vz
    @0
    wral
    #
    @103
    @54
    @107
    wcel
    #
    @39
    @100
    @108
    vz
    @0
    @38
    @100
    @108
    wi
    @35
    @36
    @37
    @54
    ssel
    adantl
    ral2imi
    @106
    @104
    @110
    @109
    wb
    @105
    vz
    @54
    @0
    @37
    cvv
    eliin
    ax-mp
    3imtr4g
    ssrdv
    ad2antll
    @61
    @107
    cX
    vz
    @0
    @3
    ciun
    #
    cdif
    #
    @7
    @61
    @29
    @107
    @112
    wceq
    @87
    vz
    @0
    cX
    @3
    iindif2
    syl
    @61
    @2
    @112
    @7
    wss
    #
    @14
    @2
    @29
    @41
    simplrl
    @2
    cS
    @111
    wss
    @113
    @1
    @111
    cS
    vz
    @0
    uniiun
    sseq2i
    cS
    @111
    cX
    sscon
    sylbi
    syl
    eqsstrd
    sstrd
    sstrd
    @9
    @65
    @67
    wa
    vz
    @63
    cJ
    @3
    @63
    wceq
    #
    @4
    @65
    @8
    @67
    @3
    @63
    cA
    eleq2
    @114
    @6
    @66
    @7
    @3
    @63
    @5
    fveq2
    sseq1d
    anbi12d
    rspcev
    syl12anc
    exlimddv
    anassrs
    pm2.61dane
    wph
    cS
    cO
    cuni
    #
    wss
    #
    @2
    vx
    @12
    wrex
    #
    wph
    vx
    cS
    @115
    wph
    @0
    cS
    wcel
    #
    @0
    @115
    wcel
    #
    wph
    @118
    wa
    #
    @0
    @54
    wcel
    #
    @58
    wa
    #
    vy
    cJ
    wrex
    #
    @119
    @120
    @121
    @47
    @54
    @46
    cin
    #
    c0
    wceq
    #
    w3a
    #
    vw
    cJ
    wrex
    #
    vy
    cJ
    wrex
    #
    @123
    @120
    @23
    @0
    cX
    wcel
    @19
    @0
    cA
    wne
    #
    @128
    wph
    @23
    @118
    hauscmplem.3
    adantr
    #
    wph
    cS
    cX
    @0
    hauscmplem.4
    sselda
    wph
    @19
    @118
    @27
    adantr
    @118
    @118
    cA
    cS
    wcel
    wn
    @129
    wph
    @118
    id
    wph
    cA
    cX
    cS
    hauscmplem.6
    eldifbd
    @0
    cA
    cS
    nelne2
    syl2anr
    @0
    cA
    vw
    vy
    cJ
    cX
    hauscmp.1
    hausnei
    syl13anc
    @120
    @127
    @122
    vy
    cJ
    @120
    @54
    cJ
    wcel
    #
    wa
    #
    @127
    @121
    @57
    wa
    #
    vw
    cJ
    wrex
    @122
    @132
    @126
    @133
    vw
    cJ
    @126
    @121
    @47
    @125
    wa
    #
    wa
    @132
    @46
    cJ
    wcel
    #
    wa
    #
    @133
    @121
    @47
    @125
    3anass
    @136
    @134
    @57
    @121
    @136
    @125
    @56
    @47
    @136
    @125
    @46
    @55
    wss
    #
    @56
    @136
    @46
    cX
    wss
    #
    @125
    @137
    wb
    @135
    @138
    @132
    @135
    @46
    @92
    cX
    @46
    cJ
    elssuni
    hauscmp.1
    syl6sseqr
    adantl
    @125
    @46
    @54
    cin
    #
    c0
    wceq
    @138
    @137
    @124
    @139
    c0
    @54
    @46
    incom
    eqeq1i
    @46
    @54
    cX
    reldisj
    syl5bb
    syl
    @136
    @55
    @83
    wcel
    #
    @137
    @56
    wi
    @132
    @140
    @135
    @120
    @22
    @131
    @140
    @120
    @23
    @22
    @130
    @24
    syl
    @54
    cJ
    cX
    hauscmp.1
    opncld
    sylan
    adantr
    @140
    @137
    @56
    @55
    @46
    cJ
    cX
    hauscmp.1
    clsss2
    ex
    syl
    sylbid
    anim2d
    anim2d
    syl5bi
    reximdva
    @121
    @57
    vw
    cJ
    r19.42v
    syl6ib
    reximdva
    mpd
    @119
    @0
    @58
    vy
    cJ
    crab
    #
    cuni
    #
    wcel
    @123
    @115
    @142
    @0
    cO
    @141
    hauscmplem.2
    unieqi
    eleq2i
    @58
    vy
    @0
    cJ
    elunirab
    bitri
    sylibr
    ex
    ssrdv
    wph
    cO
    cJ
    cpw
    #
    wcel
    #
    cS
    @3
    cuni
    #
    wss
    #
    @2
    vx
    @3
    cpw
    #
    cfn
    cin
    #
    wrex
    #
    wi
    #
    vz
    @143
    wral
    #
    @116
    @117
    wi
    #
    wph
    @144
    cO
    cJ
    wss
    #
    cO
    @141
    cJ
    hauscmplem.2
    @58
    vy
    cJ
    ssrab2
    eqsstri
    wph
    @23
    @144
    @153
    wb
    hauscmplem.3
    cO
    cJ
    cha
    elpw2g
    syl
    mpbiri
    wph
    @22
    cS
    cX
    wss
    #
    cJ
    cS
    crest
    co
    ccmp
    wcel
    #
    @151
    @25
    hauscmplem.4
    hauscmplem.5
    @22
    @154
    @155
    @151
    cS
    cJ
    cX
    vz
    vx
    hauscmp.1
    cmpsub
    biimp3a
    syl3anc
    @150
    @152
    vz
    cO
    @143
    @3
    cO
    wceq
    #
    @146
    @116
    @149
    @117
    @156
    @145
    @115
    cS
    @3
    cO
    unieq
    sseq2d
    @156
    @2
    vx
    @148
    @12
    @156
    @147
    @11
    cfn
    @3
    cO
    pweq
    ineq1d
    rexeqdv
    imbi12d
    rspcva
    syl2anc
    mpd
    r19.29a
end
