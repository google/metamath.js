include "cv.mm"
include "cfi.mm"
include "cfv.mm"
include "ctg.mm"
include "wceq.mm"
include "cuni.mm"
include "cpw.mm"
include "cfn.mm"
include "cin.mm"
include "wrex.mm"
include "wi.mm"
include "wral.mm"
include "wcel.mm"
include "w3a.mm"
include "wn.mm"
include "ralnex.mm"
include "wa.mm"
include "wpss.mm"
include "wss.mm"
include "crab.mm"
include "c0.mm"
include "csn.mm"
include "cun.mm"
include "alexsubALTlem2.mm"
include "wo.mm"
include "elun.mm"
include "weq.mm"
include "sseq2.mm"
include "pweq.mm"
include "ineq1d.mm"
include "raleqdv.mm"
include "anbi12d.mm"
include "elrab.mm"
include "velsn.mm"
include "orbi12i.mm"
include "bitri.mm"
include "simprrl.mm"
include "unissd.mm"
include "sseq1.mm"
include "syl5ibrcom.mm"
include "inss1.mm"
include "vex.mm"
include "elpw2.mm"
include "mpbir.mm"
include "unieq.mm"
include "eqeq2d.mm"
include "rexeqdv.mm"
include "imbi12d.mm"
include "rspccv.mm"
include "mpi.mm"
include "inss2.mm"
include "sstr.mm"
include "mpan2.mm"
include "anim1i.mm"
include "elfpw.mm"
include "3imtr4i.mm"
include "reximi2.mm"
include "syl6.mm"
include "cbvrexv.mm"
include "syl6ib.mm"
include "dfrex2.mm"
include "con2d.mm"
include "a1d.mm"
include "3ad2ant2.mm"
include "adantr.mm"
include "impd.mm"
include "impr.mm"
include "wb.mm"
include "unissi.mm"
include "cvv.mm"
include "fiuni.mm"
include "ax-mp.mm"
include "ctb.mm"
include "fibas.mm"
include "unitg.mm"
include "eqtr4i.mm"
include "syl6reqr.mm"
include "syl6eqr.mm"
include "3ad2ant1.mm"
include "syl5sseq.mm"
include "eqcom.mm"
include "eqss.mm"
include "baib.mm"
include "syl5bb.mm"
include "syl.mm"
include "mtbid.mm"
include "sstr2.mm"
include "con3rr3.mm"
include "wex.mm"
include "nss.mm"
include "df-rex.mm"
include "bitr4i.mm"
include "wel.mm"
include "eluni2.mm"
include "cint.mm"
include "elpwi.mm"
include "sseld.mm"
include "ad2antrl.mm"
include "elfi.mm"
include "mp2an.mm"
include "alexsubALTlem3.mm"
include "ad4antlr.mm"
include "ssfii.mm"
include "sseli.mm"
include "elpwid.mm"
include "ad2antrr.mm"
include "ad2antlr.mm"
include "simprl.mm"
include "sseldd.mm"
include "sseldi.mm"
include "snssd.mm"
include "unssd.mm"
include "fvex.mm"
include "sylibr.mm"
include "ssun1.mm"
include "syl6ss.mm"
include "notbid.mm"
include "cbvralv.mm"
include "biimpi.mm"
include "ad2antll.mm"
include "jca32.mm"
include "elun1.mm"
include "wne.mm"
include "vsnid.mm"
include "elun2.mm"
include "intss1.mm"
include "impcom.mm"
include "adantll.mm"
include "adantlr.mm"
include "adantl.mm"
include "adantrrr.mm"
include "simprlr.mm"
include "elin.mm"
include "elunii.mm"
include "ex.mm"
include "syl5bir.mm"
include "expd.mm"
include "sylc.mm"
include "con3d.mm"
include "expr.mm"
include "com23.mm"
include "exp32.mm"
include "imp55.mm"
include "eleq1.mm"
include "elequ1.mm"
include "spcev.mm"
include "sylancr.mm"
include "eqimss2.mm"
include "necon3bi.mm"
include "jctil.mm"
include "df-pss.mm"
include "psseq2.mm"
include "rspcev.mm"
include "syl2anc.mm"
include "rexlimddv.mm"
include "exp45.mm"
include "rexlimdv.mm"
include "mpdd.mm"
include "syl5bi.mm"
include "3syld.mm"
include "simpll3.mm"
include "simplr.mm"
include "biantrurd.mm"
include "bitr3d.mm"
include "sylanbrc.mm"
include "rspcv.mm"
include "id.mm"
include "0elpw.mm"
include "0fin.mm"
include "mpbir2an.mm"
include "syl6eqel.mm"
include "syl5.mm"
include "necon2ad.mm"
include "psseq1.mm"
include "0pss.mm"
include "syl6bb.mm"
include "sylibrd.mm"
include "nsyld.mm"
include "jaod.mm"
include "mpd.mm"
include "con4d.mm"
include "3exp.mm"
include "ralrimdv.mm"

theorem alexsubALTlem4
  let vx: setvar x
  let cJ: class J
  let cX: class X
  let va: setvar a
  let vb: setvar b
  let vc: setvar c
  let vd: setvar d
  let vf: setvar f
  let vm: setvar m
  let vn: setvar n
  let vs: setvar s
  let vt: setvar t
  let vu: setvar u
  let vv: setvar v
  let vw: setvar w
  let vy: setvar y
  let vz: setvar z
  assume alexsubALT.1: |- X = U. J

  disjoint a b
  disjoint a c
  disjoint a d
  disjoint a x
  disjoint J a
  disjoint b c
  disjoint b d
  disjoint b x
  disjoint J b
  disjoint c d
  disjoint c x
  disjoint J c
  disjoint d x
  disjoint J d
  disjoint J x
  disjoint X a
  disjoint X b
  disjoint X c
  disjoint X d
  disjoint X x
  disjoint a f
  disjoint a m
  disjoint a n
  disjoint a s
  disjoint a t
  disjoint a u
  disjoint a v
  disjoint a w
  disjoint a y
  disjoint a z
  disjoint b f
  disjoint b m
  disjoint b n
  disjoint b s
  disjoint b t
  disjoint b u
  disjoint b v
  disjoint b w
  disjoint b y
  disjoint b z
  disjoint c f
  disjoint c m
  disjoint c n
  disjoint c s
  disjoint c t
  disjoint c u
  disjoint c v
  disjoint c w
  disjoint c y
  disjoint c z
  disjoint d f
  disjoint d m
  disjoint d n
  disjoint d s
  disjoint d t
  disjoint d u
  disjoint d v
  disjoint d w
  disjoint d y
  disjoint d z
  disjoint f m
  disjoint f n
  disjoint f s
  disjoint f t
  disjoint f u
  disjoint f v
  disjoint f w
  disjoint f x
  disjoint f y
  disjoint f z
  disjoint J f
  disjoint m n
  disjoint m s
  disjoint m t
  disjoint m u
  disjoint m v
  disjoint m w
  disjoint m x
  disjoint m y
  disjoint m z
  disjoint J m
  disjoint n s
  disjoint n t
  disjoint n u
  disjoint n v
  disjoint n w
  disjoint n x
  disjoint n y
  disjoint n z
  disjoint J n
  disjoint s t
  disjoint s u
  disjoint s v
  disjoint s w
  disjoint s x
  disjoint s y
  disjoint s z
  disjoint J s
  disjoint t u
  disjoint t v
  disjoint t w
  disjoint t x
  disjoint t y
  disjoint t z
  disjoint J t
  disjoint u v
  disjoint u w
  disjoint u x
  disjoint u y
  disjoint u z
  disjoint J u
  disjoint v w
  disjoint v x
  disjoint v y
  disjoint v z
  disjoint J v
  disjoint w x
  disjoint w y
  disjoint w z
  disjoint J w
  disjoint x y
  disjoint x z
  disjoint y z
  disjoint J y
  disjoint J z
  disjoint X f
  disjoint X m
  disjoint X n
  disjoint X s
  disjoint X t
  disjoint X u
  disjoint X v
  disjoint X w
  disjoint X y
  disjoint X z
  assert |- ( J = ( topGen ` ( fi ` x ) ) -> ( A. c e. ~P x ( X = U. c -> E. d e. ( ~P c i^i Fin ) X = U. d ) -> A. a e. ~P ( fi ` x ) ( X = U. a -> E. b e. ( ~P a i^i Fin ) X = U. b ) ) )

  proof
    cJ
    vx
    cv
    #
    cfi
    cfv
    #
    ctg
    cfv
    #
    wceq
    #
    cX
    vc
    cv
    #
    cuni
    #
    wceq
    #
    cX
    vd
    cv
    #
    cuni
    #
    wceq
    #
    vd
    @4
    cpw
    #
    cfn
    cin
    #
    wrex
    #
    wi
    #
    vc
    @0
    cpw
    #
    wral
    #
    cX
    va
    cv
    #
    cuni
    #
    wceq
    #
    cX
    vb
    cv
    #
    cuni
    #
    wceq
    #
    vb
    @16
    cpw
    #
    cfn
    cin
    #
    wrex
    #
    wi
    #
    va
    @1
    cpw
    #
    @3
    @15
    @16
    @26
    wcel
    #
    @25
    @3
    @15
    @27
    w3a
    #
    @24
    @18
    @24
    wn
    @21
    wn
    #
    vb
    @23
    wral
    #
    @28
    @18
    wn
    #
    @21
    vb
    @23
    ralnex
    @28
    @30
    @31
    @28
    @30
    wa
    #
    vu
    cv
    #
    vv
    cv
    #
    wpss
    #
    wn
    #
    vv
    @16
    vz
    cv
    #
    wss
    #
    @29
    vb
    @37
    cpw
    #
    cfn
    cin
    #
    wral
    #
    wa
    #
    vz
    @26
    crab
    #
    c0
    csn
    #
    cun
    #
    wral
    #
    vu
    @45
    wrex
    @31
    vx
    vz
    vv
    vu
    cJ
    cX
    va
    vb
    vc
    vd
    alexsubALT.1
    alexsubALTlem2
    @32
    @46
    @31
    vu
    @45
    @33
    @45
    wcel
    #
    @33
    @26
    wcel
    #
    @16
    @33
    wss
    #
    @29
    vb
    @33
    cpw
    #
    cfn
    cin
    #
    wral
    #
    wa
    #
    wa
    #
    @33
    c0
    wceq
    #
    wo
    #
    @32
    @46
    @31
    wi
    #
    @47
    @33
    @43
    wcel
    #
    @33
    @44
    wcel
    #
    wo
    @56
    @33
    @43
    @44
    elun
    @58
    @54
    @59
    @55
    @42
    @53
    vz
    @33
    @26
    vz
    vu
    weq
    #
    @38
    @49
    @41
    @52
    @37
    @33
    @16
    sseq2
    @60
    @29
    vb
    @40
    @51
    @60
    @39
    @50
    cfn
    @37
    @33
    pweq
    ineq1d
    raleqdv
    anbi12d
    elrab
    vu
    c0
    velsn
    orbi12i
    bitri
    @32
    @54
    @57
    @55
    @28
    @54
    @57
    wi
    @30
    @28
    @54
    @57
    @46
    @35
    vv
    @45
    wrex
    #
    wn
    @28
    @54
    wa
    #
    @31
    @35
    vv
    @45
    ralnex
    @62
    @18
    @61
    @62
    @18
    cX
    @33
    cuni
    #
    wss
    #
    @63
    @0
    @33
    cin
    #
    cuni
    #
    wss
    #
    wn
    #
    @61
    @62
    @64
    @18
    @17
    @63
    wss
    @62
    @16
    @33
    @28
    @48
    @49
    @52
    simprrl
    unissd
    cX
    @17
    @63
    sseq1
    syl5ibrcom
    @62
    cX
    @66
    wss
    #
    wn
    @64
    @68
    wi
    @62
    cX
    @66
    wceq
    #
    @69
    @28
    @48
    @53
    @70
    wn
    #
    @28
    @48
    wa
    @49
    @52
    @71
    @28
    @49
    @52
    @71
    wi
    #
    wi
    #
    @48
    @15
    @3
    @73
    @27
    @15
    @72
    @49
    @15
    @70
    @52
    @15
    @70
    @21
    vb
    @51
    wrex
    #
    @52
    wn
    @15
    @70
    @9
    vd
    @51
    wrex
    #
    @74
    @15
    @70
    @9
    vd
    @65
    cpw
    #
    cfn
    cin
    #
    wrex
    #
    @75
    @15
    @65
    @14
    wcel
    #
    @70
    @78
    wi
    #
    @79
    @65
    @0
    wss
    @0
    @33
    inss1
    #
    @65
    @0
    vx
    vex
    #
    elpw2
    mpbir
    @13
    @80
    vc
    @65
    @14
    @4
    @65
    wceq
    #
    @6
    @70
    @12
    @78
    @83
    @5
    @66
    cX
    @4
    @65
    unieq
    eqeq2d
    @83
    @9
    vd
    @11
    @77
    @83
    @10
    @76
    cfn
    @4
    @65
    pweq
    ineq1d
    rexeqdv
    imbi12d
    rspccv
    mpi
    @9
    @9
    vd
    @77
    @51
    @7
    @77
    wcel
    #
    @7
    @51
    wcel
    #
    @9
    @7
    @65
    wss
    #
    @7
    cfn
    wcel
    #
    wa
    @7
    @33
    wss
    #
    @87
    wa
    @84
    @85
    @86
    @88
    @87
    @86
    @65
    @33
    wss
    @88
    @0
    @33
    inss2
    @7
    @65
    @33
    sstr
    mpan2
    anim1i
    @7
    @65
    elfpw
    @7
    @33
    elfpw
    3imtr4i
    anim1i
    reximi2
    syl6
    @9
    @21
    vd
    vb
    @51
    vd
    vb
    weq
    @8
    @20
    cX
    @7
    @19
    unieq
    eqeq2d
    cbvrexv
    syl6ib
    @21
    vb
    @51
    dfrex2
    syl6ib
    con2d
    a1d
    3ad2ant2
    adantr
    impd
    impr
    @62
    @66
    cX
    wss
    #
    @70
    @69
    wb
    @62
    @0
    cuni
    #
    @66
    cX
    @65
    @0
    @81
    unissi
    @28
    @90
    cX
    wceq
    #
    @54
    @3
    @15
    @91
    @27
    @3
    @90
    cJ
    cuni
    #
    cX
    @3
    @92
    @2
    cuni
    #
    @90
    cJ
    @2
    unieq
    @90
    @1
    cuni
    #
    @93
    @0
    cvv
    wcel
    #
    @90
    @94
    wceq
    @82
    @0
    cvv
    fiuni
    ax-mp
    @1
    ctb
    wcel
    @93
    @94
    wceq
    @0
    fibas
    @1
    ctb
    unitg
    ax-mp
    eqtr4i
    syl6reqr
    alexsubALT.1
    syl6eqr
    3ad2ant1
    adantr
    syl5sseq
    @70
    @66
    cX
    wceq
    #
    @89
    @69
    cX
    @66
    eqcom
    @96
    @89
    @69
    @66
    cX
    eqss
    baib
    syl5bb
    syl
    mtbid
    @64
    @67
    @69
    cX
    @63
    @66
    sstr2
    con3rr3
    syl
    @68
    vy
    cv
    #
    @66
    wcel
    #
    wn
    #
    vy
    @63
    wrex
    #
    @62
    @61
    @68
    @97
    @63
    wcel
    #
    @99
    wa
    vy
    wex
    @100
    vy
    @63
    @66
    nss
    @99
    vy
    @63
    df-rex
    bitr4i
    @62
    @99
    @61
    vy
    @63
    @101
    vy
    vw
    wel
    #
    vw
    @33
    wrex
    @62
    @99
    @61
    wi
    #
    vw
    @97
    @33
    eluni2
    @62
    @102
    @103
    vw
    @33
    @62
    vw
    vu
    wel
    #
    vw
    cv
    #
    vt
    cv
    #
    cint
    #
    wceq
    #
    vt
    @14
    cfn
    cin
    #
    wrex
    #
    @102
    @103
    wi
    #
    @62
    @104
    @105
    @1
    wcel
    #
    @110
    @48
    @104
    @112
    wi
    @28
    @53
    @48
    @33
    @1
    @105
    @33
    @1
    elpwi
    #
    sseld
    ad2antrl
    @105
    cvv
    wcel
    @95
    @112
    @110
    wb
    vw
    vex
    @82
    vt
    @105
    @0
    cvv
    cvv
    elfi
    mp2an
    syl6ib
    @62
    @104
    @110
    @111
    wi
    @62
    @104
    wa
    #
    @108
    @111
    vt
    @109
    @114
    @106
    @109
    wcel
    #
    @108
    @111
    @114
    @115
    @108
    wa
    #
    @102
    @99
    @61
    @114
    @116
    @102
    @99
    wa
    #
    wa
    #
    wa
    #
    cX
    vn
    cv
    #
    cuni
    #
    wceq
    #
    wn
    #
    vn
    @33
    vs
    cv
    #
    csn
    #
    cun
    #
    cpw
    #
    cfn
    cin
    #
    wral
    #
    @61
    vs
    @106
    vx
    vy
    vw
    vu
    vt
    vn
    cJ
    cX
    vs
    va
    vb
    vc
    vd
    alexsubALT.1
    alexsubALTlem3
    @119
    vs
    vt
    wel
    #
    @129
    wa
    #
    wa
    #
    @126
    @45
    wcel
    #
    @33
    @126
    wpss
    #
    @61
    @132
    @126
    @43
    wcel
    #
    @133
    @132
    @126
    @26
    wcel
    #
    @16
    @126
    wss
    #
    @29
    vb
    @128
    wral
    #
    wa
    #
    wa
    @135
    @132
    @136
    @137
    @138
    @132
    @126
    @1
    wss
    @136
    @132
    @33
    @125
    @1
    @54
    @33
    @1
    wss
    #
    @28
    @104
    @118
    @131
    @48
    @140
    @53
    @113
    adantr
    ad4antlr
    @132
    @124
    @1
    @132
    @0
    @1
    @124
    @95
    @0
    @1
    wss
    @82
    @0
    cvv
    ssfii
    ax-mp
    @132
    @106
    @0
    @124
    @118
    @106
    @0
    wss
    #
    @114
    @131
    @115
    @141
    @108
    @117
    @115
    @106
    @0
    @109
    @14
    @106
    @14
    cfn
    inss1
    sseli
    elpwid
    #
    ad2antrr
    ad2antlr
    @119
    @130
    @129
    simprl
    sseldd
    sseldi
    snssd
    unssd
    @126
    @1
    @0
    cfi
    fvex
    elpw2
    sylibr
    @132
    @16
    @33
    @126
    @54
    @49
    @28
    @104
    @118
    @131
    @48
    @49
    @52
    simprl
    ad4antlr
    @33
    @125
    ssun1
    #
    syl6ss
    @129
    @138
    @119
    @130
    @129
    @138
    @123
    @29
    vn
    vb
    @128
    vn
    vb
    weq
    #
    @122
    @21
    @144
    @121
    @20
    cX
    @120
    @19
    unieq
    eqeq2d
    notbid
    cbvralv
    biimpi
    ad2antll
    jca32
    @42
    @139
    vz
    @126
    @26
    @37
    @126
    wceq
    #
    @38
    @137
    @41
    @138
    @37
    @126
    @16
    sseq2
    @145
    @29
    vb
    @40
    @128
    @145
    @39
    @127
    cfn
    @37
    @126
    pweq
    ineq1d
    raleqdv
    anbi12d
    elrab
    sylibr
    @126
    @43
    @44
    elun1
    syl
    @132
    @33
    @126
    wss
    #
    @33
    @126
    wne
    #
    wa
    @134
    @132
    @147
    @146
    @132
    @126
    @33
    wss
    #
    wn
    #
    @147
    @132
    @34
    @126
    wcel
    #
    vv
    vu
    wel
    #
    wn
    #
    wa
    #
    vv
    wex
    #
    @149
    @132
    @124
    @126
    wcel
    #
    vs
    vu
    wel
    #
    wn
    #
    @154
    @124
    @125
    wcel
    @155
    vs
    vsnid
    @124
    @125
    @33
    elun2
    ax-mp
    @114
    @116
    @102
    @99
    @131
    @157
    @114
    @116
    @102
    @99
    @131
    @157
    wi
    wi
    @114
    @116
    @102
    wa
    #
    wa
    @131
    @99
    @157
    @114
    @158
    @131
    @99
    @157
    wi
    @114
    @158
    @131
    wa
    #
    wa
    #
    @156
    @98
    @160
    vy
    vs
    wel
    #
    vs
    vx
    wel
    #
    @156
    @98
    wi
    @160
    @105
    @124
    @97
    @104
    @159
    @105
    @124
    wss
    #
    @62
    @104
    @158
    @130
    @163
    @129
    @158
    @130
    wa
    @163
    @104
    @116
    @130
    @163
    @102
    @108
    @130
    @163
    @115
    @130
    @108
    @163
    @130
    @163
    @108
    @107
    @124
    wss
    @124
    @106
    intss1
    @105
    @107
    @124
    sseq1
    syl5ibrcom
    impcom
    adantll
    adantlr
    adantl
    adantrrr
    adantll
    @114
    @116
    @102
    @131
    simprlr
    sseldd
    @160
    @106
    @0
    @124
    @158
    @141
    @114
    @131
    @115
    @141
    @108
    @102
    @142
    ad2antrr
    ad2antrl
    @114
    @158
    @130
    @129
    simprrl
    sseldd
    @161
    @162
    @156
    @98
    @162
    @156
    wa
    @124
    @65
    wcel
    #
    @161
    @98
    @124
    @0
    @33
    elin
    @161
    @164
    @98
    @97
    @124
    @65
    elunii
    ex
    syl5bir
    expd
    sylc
    con3d
    expr
    com23
    exp32
    imp55
    @153
    @155
    @157
    wa
    vv
    @124
    vs
    vex
    vv
    vs
    weq
    #
    @150
    @155
    @152
    @157
    @34
    @124
    @126
    eleq1
    @165
    @151
    @156
    vv
    vs
    vu
    elequ1
    notbid
    anbi12d
    spcev
    sylancr
    vv
    @126
    @33
    nss
    sylibr
    @148
    @33
    @126
    @126
    @33
    eqimss2
    necon3bi
    syl
    @143
    jctil
    @33
    @126
    df-pss
    sylibr
    @35
    @134
    vv
    @126
    @45
    @34
    @126
    @33
    psseq2
    rspcev
    syl2anc
    rexlimddv
    exp45
    expd
    rexlimdv
    ex
    mpdd
    rexlimdv
    syl5bi
    rexlimdv
    syl5bi
    3syld
    con3d
    syl5bi
    ex
    adantr
    @32
    @55
    @57
    @32
    @55
    wa
    #
    @46
    @33
    @16
    wpss
    #
    @18
    @166
    @16
    @45
    wcel
    @46
    @167
    wn
    #
    wi
    @166
    @43
    @45
    @16
    @43
    @44
    ssun1
    @166
    @27
    @30
    @16
    @43
    wcel
    @3
    @15
    @27
    @30
    @55
    simpll3
    @28
    @30
    @55
    simplr
    @42
    @30
    vz
    @16
    @26
    vz
    va
    weq
    #
    @41
    @42
    @30
    @169
    @38
    @41
    @16
    @37
    eqimss2
    biantrurd
    @169
    @29
    vb
    @40
    @23
    @169
    @39
    @22
    cfn
    @37
    @16
    pweq
    ineq1d
    raleqdv
    bitr3d
    elrab
    sylanbrc
    sseldi
    @36
    @168
    vv
    @16
    @45
    vv
    va
    weq
    @35
    @167
    @34
    @16
    @33
    psseq2
    notbid
    rspcv
    syl
    @166
    @18
    @16
    c0
    wne
    #
    @167
    @30
    @18
    @170
    wi
    @28
    @55
    @30
    @18
    @16
    c0
    @16
    c0
    wceq
    #
    @16
    @23
    wcel
    @30
    @31
    @171
    @16
    c0
    @23
    @171
    id
    c0
    @23
    wcel
    c0
    @22
    wcel
    c0
    cfn
    wcel
    @16
    0elpw
    0fin
    c0
    @22
    cfn
    elin
    mpbir2an
    syl6eqel
    @29
    @31
    vb
    @16
    @23
    vb
    va
    weq
    #
    @21
    @18
    @172
    @20
    @17
    cX
    @19
    @16
    unieq
    eqeq2d
    notbid
    rspccv
    syl5
    necon2ad
    ad2antlr
    @166
    @167
    c0
    @16
    wpss
    #
    @170
    @55
    @167
    @173
    wb
    @32
    @33
    c0
    @16
    psseq1
    adantl
    @16
    0pss
    syl6bb
    sylibrd
    nsyld
    ex
    jaod
    syl5bi
    rexlimdv
    mpd
    ex
    syl5bir
    con4d
    3exp
    ralrimdv
end
