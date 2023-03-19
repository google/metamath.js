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
include "wss.mm"
include "wn.mm"
include "wa.mm"
include "wel.mm"
include "cint.mm"
include "csn.mm"
include "cun.mm"
include "dfrex2.mm"
include "ralbii.mm"
include "ralnex.mm"
include "bitr2i.mm"
include "wf.mm"
include "wex.mm"
include "cdif.mm"
include "elin.mm"
include "elpwi.mm"
include "adantr.mm"
include "uncom.mm"
include "syl6sseq.mm"
include "ssundif.mm"
include "sylib.mm"
include "diffi.mm"
include "adantl.mm"
include "jca.mm"
include "sylbi.mm"
include "ad2antll.mm"
include "vex.mm"
include "elpw2.mm"
include "anbi1i.mm"
include "simprrr.mm"
include "eldif.mm"
include "simplbi2.mm"
include "wo.mm"
include "elun.mm"
include "orcom.mm"
include "bitr4i.mm"
include "df-or.mm"
include "ssriv.mm"
include "uniss.mm"
include "mp1i.mm"
include "uniun.mm"
include "unisn.mm"
include "uneq2i.mm"
include "eqtri.mm"
include "eqsstrd.mm"
include "difss.mm"
include "unissi.mm"
include "sseq2.mm"
include "mpbiri.mm"
include "inss1.mm"
include "sseli.mm"
include "elpwid.mm"
include "ad3antrrr.mm"
include "ad2antlr.mm"
include "simprl.mm"
include "sseldd.mm"
include "elssuni.mm"
include "syl.mm"
include "ctb.mm"
include "fibas.mm"
include "unitg.mm"
include "unieq.mm"
include "3ad2ant1.mm"
include "cvv.mm"
include "fiuni.mm"
include "3eqtr4rd.mm"
include "syl6eqr.mm"
include "sseqtrd.mm"
include "unssd.mm"
include "eqssd.mm"
include "uneq1d.mm"
include "eqeq2d.mm"
include "rspcev.mm"
include "syl2anc.mm"
include "expr.mm"
include "expd.mm"
include "rexlimdv.mm"
include "ralimdva.mm"
include "inss2.mm"
include "ac6sfi.mm"
include "ex.mm"
include "ad2antrl.mm"
include "ciun.mm"
include "ffvelrn.mm"
include "ralrimiva.mm"
include "iunss.mm"
include "sylibr.mm"
include "simplrr.mm"
include "snssd.mm"
include "sseldi.mm"
include "iunfi.mm"
include "syl2an.mm"
include "adantlr.mm"
include "ad2ant2lr.mm"
include "snfi.mm"
include "unfi.mm"
include "sylancl.mm"
include "wal.mm"
include "imbi2i.mm"
include "albii.mm"
include "alinexa.mm"
include "weq.mm"
include "fveq2.mm"
include "unieqd.mm"
include "id.mm"
include "uneq12d.mm"
include "rspcv.mm"
include "eleq2.mm"
include "biimpd.mm"
include "eluni.mm"
include "orbi1i.mm"
include "imbi1i.mm"
include "3bitri.mm"
include "eleq1.mm"
include "notbid.mm"
include "ralbidv.mm"
include "imbi12d.mm"
include "spv.mm"
include "eleq2d.mm"
include "syl9r.mm"
include "alrimdv.mm"
include "imim1d.mm"
include "syl5bi.mm"
include "a1dd.mm"
include "syld.mm"
include "com14.mm"
include "imp31.mm"
include "com23.mm"
include "ralrimdv.mm"
include "elint2.mm"
include "syl6ibr.mm"
include "wb.mm"
include "ad2antrr.mm"
include "sylibrd.mm"
include "orrd.mm"
include "orc.mm"
include "anim2i.mm"
include "eximi.mm"
include "equid.mm"
include "equequ1.mm"
include "anbi12d.mm"
include "spcev.mm"
include "mpan2.mm"
include "olc.mm"
include "jaoi.mm"
include "eliun.mm"
include "velsn.mm"
include "orbi12i.mm"
include "bitri.mm"
include "anbi2i.mm"
include "exbii.mm"
include "syl6.mm"
include "adantll.mm"
include "ad2ant2l.mm"
include "ssrdv.mm"
include "nfra1.mm"
include "nfv.mm"
include "rsp.mm"
include "eqimss2.mm"
include "ssun3.mm"
include "sstr.mm"
include "expcom.mm"
include "syl2im.mm"
include "rexlimd.mm"
include "ax-mp.mm"
include "syl6req.mm"
include "sseq1.mm"
include "syl5ibrcom.mm"
include "jaod.mm"
include "ralrimiv.mm"
include "unissb.mm"
include "exlimdv.mm"
include "3syld.mm"
include "syl6ib.mm"
include "con4d.mm"
include "exp32.mm"
include "com24.mm"
include "imp45.mm"

theorem alexsubALTlem3
  let vx: setvar x
  let vy: setvar y
  let vw: setvar w
  let vu: setvar u
  let vt: setvar t
  let vn: setvar n
  let cJ: class J
  let cX: class X
  let vs: setvar s
  let va: setvar a
  let vb: setvar b
  let vc: setvar c
  let vd: setvar d
  let vf: setvar f
  let vm: setvar m
  let vv: setvar v
  let vz: setvar z
  assume alexsubALT.1: |- X = U. J

  disjoint a b
  disjoint a c
  disjoint a d
  disjoint a n
  disjoint a s
  disjoint a t
  disjoint a u
  disjoint a w
  disjoint a x
  disjoint a y
  disjoint J a
  disjoint b c
  disjoint b d
  disjoint b n
  disjoint b s
  disjoint b t
  disjoint b u
  disjoint b w
  disjoint b x
  disjoint b y
  disjoint J b
  disjoint c d
  disjoint c n
  disjoint c s
  disjoint c t
  disjoint c u
  disjoint c w
  disjoint c x
  disjoint c y
  disjoint J c
  disjoint d n
  disjoint d s
  disjoint d t
  disjoint d u
  disjoint d w
  disjoint d x
  disjoint d y
  disjoint J d
  disjoint n s
  disjoint n t
  disjoint n u
  disjoint n w
  disjoint n x
  disjoint n y
  disjoint J n
  disjoint s t
  disjoint s u
  disjoint s w
  disjoint s x
  disjoint s y
  disjoint J s
  disjoint t u
  disjoint t w
  disjoint t x
  disjoint t y
  disjoint J t
  disjoint u w
  disjoint u x
  disjoint u y
  disjoint J u
  disjoint w x
  disjoint w y
  disjoint J w
  disjoint x y
  disjoint J x
  disjoint J y
  disjoint X a
  disjoint X b
  disjoint X c
  disjoint X d
  disjoint X n
  disjoint X s
  disjoint X t
  disjoint X u
  disjoint X w
  disjoint X x
  disjoint X y
  disjoint a f
  disjoint a m
  disjoint a v
  disjoint a z
  disjoint b f
  disjoint b m
  disjoint b v
  disjoint b z
  disjoint c f
  disjoint c m
  disjoint c v
  disjoint c z
  disjoint d f
  disjoint d m
  disjoint d v
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
  disjoint n v
  disjoint n z
  disjoint s v
  disjoint s z
  disjoint t v
  disjoint t z
  disjoint u v
  disjoint u z
  disjoint v w
  disjoint v x
  disjoint v y
  disjoint v z
  disjoint J v
  disjoint w z
  disjoint x z
  disjoint y z
  disjoint J z
  disjoint X f
  disjoint X m
  disjoint X v
  disjoint X z
  assert |- ( ( ( ( ( J = ( topGen ` ( fi ` x ) ) /\ A. c e. ~P x ( X = U. c -> E. d e. ( ~P c i^i Fin ) X = U. d ) /\ a e. ~P ( fi ` x ) ) /\ ( u e. ~P ( fi ` x ) /\ ( a C_ u /\ A. b e. ( ~P u i^i Fin ) -. X = U. b ) ) ) /\ w e. u ) /\ ( ( t e. ( ~P x i^i Fin ) /\ w = |^| t ) /\ ( y e. w /\ -. y e. U. ( x i^i u ) ) ) ) -> E. s e. t A. n e. ( ~P ( u u. { s } ) i^i Fin ) -. X = U. n )

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
    wceq
    cX
    vd
    cv
    cuni
    wceq
    vd
    @4
    cpw
    cfn
    cin
    wrex
    wi
    vc
    @0
    cpw
    #
    wral
    #
    va
    cv
    #
    @1
    cpw
    #
    wcel
    #
    w3a
    #
    vu
    cv
    #
    @8
    wcel
    #
    @7
    @11
    wss
    #
    cX
    vb
    cv
    #
    cuni
    #
    wceq
    #
    wn
    vb
    @11
    cpw
    #
    cfn
    cin
    #
    wral
    #
    wa
    wa
    wa
    vw
    vu
    wel
    #
    vt
    cv
    #
    @5
    cfn
    cin
    #
    wcel
    #
    vw
    cv
    #
    @21
    cint
    #
    wceq
    #
    wa
    #
    vy
    vw
    wel
    vy
    cv
    #
    @0
    @11
    cin
    cuni
    wcel
    wn
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
    vn
    @11
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
    vs
    @21
    wrex
    #
    @10
    @12
    @13
    @19
    @20
    @30
    @40
    wi
    wi
    #
    @10
    @12
    @13
    @19
    @41
    wi
    @10
    @12
    @13
    wa
    #
    wa
    #
    @30
    @20
    @19
    @40
    @43
    @30
    @20
    @19
    @40
    wi
    @43
    @30
    @20
    wa
    #
    wa
    #
    @40
    @19
    @45
    @40
    wn
    #
    @16
    vb
    @18
    wrex
    #
    @19
    wn
    @46
    @33
    vn
    @38
    wrex
    #
    vs
    @21
    wral
    #
    @45
    @47
    @49
    @39
    wn
    #
    vs
    @21
    wral
    @46
    @48
    @50
    vs
    @21
    @33
    vn
    @38
    dfrex2
    ralbii
    @39
    vs
    @21
    ralnex
    bitr2i
    @45
    @49
    cX
    vm
    cv
    #
    cuni
    #
    @34
    cun
    #
    wceq
    #
    vm
    @18
    wrex
    #
    vs
    @21
    wral
    #
    @21
    @18
    vf
    cv
    #
    wf
    #
    cX
    @34
    @57
    cfv
    #
    cuni
    #
    @34
    cun
    #
    wceq
    #
    vs
    @21
    wral
    #
    wa
    #
    vf
    wex
    #
    @47
    @45
    @48
    @55
    vs
    @21
    @45
    vs
    vt
    wel
    #
    wa
    #
    @33
    @55
    vn
    @38
    @67
    @31
    @38
    wcel
    #
    @33
    @55
    @45
    @66
    @68
    @33
    wa
    #
    @55
    @45
    @66
    @69
    wa
    #
    wa
    #
    @31
    @35
    cdif
    #
    @18
    wcel
    #
    cX
    @72
    cuni
    #
    @34
    cun
    #
    wceq
    #
    @55
    @71
    @72
    @11
    wss
    #
    @72
    cfn
    wcel
    #
    wa
    #
    @73
    @69
    @79
    @45
    @66
    @68
    @79
    @33
    @68
    @31
    @37
    wcel
    #
    @31
    cfn
    wcel
    #
    wa
    #
    @79
    @31
    @37
    cfn
    elin
    @82
    @77
    @78
    @82
    @31
    @35
    @11
    cun
    #
    wss
    @77
    @82
    @31
    @36
    @83
    @80
    @31
    @36
    wss
    @81
    @31
    @36
    elpwi
    adantr
    @11
    @35
    uncom
    syl6sseq
    @31
    @35
    @11
    ssundif
    sylib
    @81
    @78
    @80
    @31
    @35
    diffi
    adantl
    jca
    sylbi
    adantr
    ad2antll
    @73
    @72
    @17
    wcel
    #
    @78
    wa
    @79
    @72
    @17
    cfn
    elin
    @84
    @77
    @78
    @72
    @11
    vu
    vex
    #
    elpw2
    anbi1i
    bitr2i
    sylib
    @71
    cX
    @75
    @71
    cX
    @32
    @75
    @45
    @66
    @68
    @33
    simprrr
    @71
    @32
    @72
    @35
    cun
    #
    cuni
    #
    @75
    @31
    @86
    wss
    @32
    @87
    wss
    @71
    vx
    @31
    @86
    vx
    vn
    wel
    #
    @0
    @35
    wcel
    #
    wn
    #
    @0
    @72
    wcel
    #
    wi
    #
    @0
    @86
    wcel
    #
    @91
    @88
    @90
    @0
    @31
    @35
    eldif
    simplbi2
    @93
    @89
    @91
    wo
    #
    @92
    @93
    @91
    @89
    wo
    @94
    @0
    @72
    @35
    elun
    @89
    @91
    orcom
    bitr4i
    @89
    @91
    df-or
    bitr2i
    sylib
    ssriv
    @31
    @86
    uniss
    mp1i
    @87
    @74
    @35
    cuni
    #
    cun
    @75
    @72
    @35
    uniun
    @95
    @34
    @74
    @34
    vs
    vex
    unisn
    uneq2i
    eqtri
    syl6sseq
    eqsstrd
    @71
    @74
    @34
    cX
    @69
    @74
    cX
    wss
    #
    @45
    @66
    @33
    @96
    @68
    @33
    @96
    @74
    @32
    wss
    @72
    @31
    @31
    @35
    difss
    unissi
    cX
    @32
    @74
    sseq2
    mpbiri
    adantl
    ad2antll
    @71
    @34
    @0
    cuni
    #
    cX
    @71
    vs
    vx
    wel
    @34
    @97
    wss
    @71
    @21
    @0
    @34
    @44
    @21
    @0
    wss
    #
    @43
    @70
    @23
    @98
    @26
    @29
    @20
    @23
    @21
    @0
    @22
    @5
    @21
    @5
    cfn
    inss1
    sseli
    elpwid
    ad3antrrr
    ad2antlr
    @45
    @66
    @69
    simprl
    sseldd
    @34
    @0
    elssuni
    syl
    @71
    @97
    cJ
    cuni
    #
    cX
    @71
    @2
    cuni
    #
    @1
    cuni
    #
    @99
    @97
    @1
    ctb
    wcel
    #
    @100
    @101
    wceq
    #
    @71
    @0
    fibas
    #
    @1
    ctb
    unitg
    #
    mp1i
    @10
    @99
    @100
    wceq
    #
    @42
    @44
    @70
    @3
    @6
    @106
    @9
    cJ
    @2
    unieq
    #
    3ad2ant1
    ad3antrrr
    @0
    cvv
    wcel
    @97
    @101
    wceq
    @71
    vx
    vex
    @0
    cvv
    fiuni
    mp1i
    3eqtr4rd
    alexsubALT.1
    syl6eqr
    sseqtrd
    unssd
    eqssd
    @54
    @76
    vm
    @72
    @18
    @51
    @72
    wceq
    #
    @53
    @75
    cX
    @108
    @52
    @74
    @34
    @51
    @72
    unieq
    uneq1d
    eqeq2d
    rspcev
    syl2anc
    expr
    expd
    rexlimdv
    ralimdva
    @30
    @56
    @65
    wi
    #
    @43
    @20
    @27
    @109
    @29
    @27
    @21
    cfn
    wcel
    #
    @109
    @23
    @110
    @26
    @22
    cfn
    @21
    @5
    cfn
    inss2
    sseli
    adantr
    #
    @110
    @56
    @65
    @54
    @62
    vs
    vm
    @21
    @18
    vf
    @51
    @59
    wceq
    #
    @53
    @61
    cX
    @112
    @52
    @60
    @34
    @51
    @59
    unieq
    uneq1d
    eqeq2d
    ac6sfi
    ex
    syl
    adantr
    ad2antrl
    @45
    @64
    @47
    vf
    @45
    @64
    @47
    @45
    @64
    wa
    #
    vs
    @21
    @59
    ciun
    #
    @24
    csn
    #
    cun
    #
    @18
    wcel
    #
    cX
    @116
    cuni
    #
    wceq
    #
    @47
    @113
    @116
    @11
    wss
    #
    @116
    cfn
    wcel
    #
    wa
    #
    @117
    @113
    @120
    @121
    @113
    @114
    @115
    @11
    @58
    @114
    @11
    wss
    #
    @45
    @63
    @58
    @59
    @11
    wss
    #
    vs
    @21
    wral
    @123
    @58
    @124
    vs
    @21
    @58
    @66
    wa
    #
    @59
    @18
    wcel
    #
    @124
    @21
    @18
    @34
    @57
    ffvelrn
    #
    @126
    @59
    @17
    wcel
    #
    @59
    cfn
    wcel
    #
    wa
    @124
    @59
    @17
    cfn
    elin
    @128
    @124
    @129
    @59
    @11
    elpwi
    adantr
    sylbi
    syl
    ralrimiva
    vs
    @21
    @59
    @11
    iunss
    sylibr
    ad2antrl
    @113
    @24
    @11
    @43
    @30
    @20
    @64
    simplrr
    #
    snssd
    unssd
    @113
    @114
    cfn
    wcel
    #
    @115
    cfn
    wcel
    @121
    @44
    @58
    @131
    @43
    @63
    @30
    @58
    @131
    @20
    @27
    @58
    @131
    @29
    @27
    @110
    @129
    vs
    @21
    wral
    @131
    @58
    @111
    @58
    @129
    vs
    @21
    @125
    @18
    cfn
    @59
    @17
    cfn
    inss2
    @127
    sseldi
    ralrimiva
    vs
    @21
    @59
    iunfi
    syl2an
    adantlr
    adantlr
    ad2ant2lr
    @24
    snfi
    @114
    @115
    unfi
    sylancl
    jca
    @117
    @116
    @17
    wcel
    #
    @121
    wa
    @122
    @116
    @17
    cfn
    elin
    @132
    @120
    @121
    @116
    @11
    @85
    elpw2
    anbi1i
    bitr2i
    sylib
    @113
    cX
    @118
    @113
    vv
    cX
    @118
    @44
    @63
    vv
    cv
    #
    cX
    wcel
    #
    @133
    @118
    wcel
    #
    wi
    #
    @43
    @58
    @30
    @63
    @136
    @20
    @27
    @63
    @136
    @29
    @26
    @63
    @136
    @23
    @26
    @63
    wa
    #
    @134
    vv
    vy
    wel
    #
    @28
    @59
    wcel
    #
    vs
    @21
    wrex
    #
    wa
    #
    vy
    wex
    #
    vv
    vw
    wel
    #
    wo
    #
    @135
    @137
    @134
    @144
    @137
    @134
    wa
    #
    @142
    @143
    @142
    wn
    #
    @138
    @139
    wn
    #
    vs
    @21
    wral
    #
    wi
    #
    vy
    wal
    #
    @145
    @143
    @150
    @138
    @140
    wn
    #
    wi
    #
    vy
    wal
    @146
    @149
    @152
    vy
    @148
    @151
    @138
    @139
    vs
    @21
    ralnex
    imbi2i
    albii
    @138
    @140
    vy
    alinexa
    bitr2i
    @145
    @150
    @133
    @25
    wcel
    #
    @143
    @145
    @150
    vv
    vz
    wel
    #
    vz
    @21
    wral
    @153
    @145
    @150
    @154
    vz
    @21
    @145
    vz
    vt
    wel
    #
    @150
    @154
    @26
    @63
    @134
    @155
    @150
    @154
    wi
    #
    wi
    @155
    @63
    @134
    @26
    @156
    @155
    @63
    cX
    vz
    cv
    #
    @57
    cfv
    #
    cuni
    #
    @157
    cun
    #
    wceq
    #
    @134
    @26
    @156
    wi
    #
    wi
    @62
    @161
    vs
    @157
    @21
    vs
    vz
    weq
    #
    @61
    @160
    cX
    @163
    @60
    @159
    @34
    @157
    @163
    @59
    @158
    @34
    @157
    @57
    fveq2
    #
    unieqd
    @163
    id
    uneq12d
    eqeq2d
    rspcv
    @161
    @134
    @133
    @160
    wcel
    #
    @155
    @162
    @161
    @134
    @165
    cX
    @160
    @133
    eleq2
    biimpd
    @155
    @165
    @156
    @26
    @165
    @143
    @24
    @158
    wcel
    #
    wn
    #
    wi
    #
    vw
    wal
    #
    @154
    wi
    #
    @155
    @156
    @165
    @133
    @159
    wcel
    #
    @154
    wo
    @143
    @166
    wa
    vw
    wex
    #
    @154
    wo
    #
    @170
    @133
    @159
    @157
    elun
    @171
    @172
    @154
    vw
    @133
    @158
    eluni
    orbi1i
    @173
    @172
    wn
    #
    @154
    wi
    @170
    @172
    @154
    df-or
    @169
    @174
    @154
    @143
    @166
    vw
    alinexa
    imbi1i
    bitr4i
    3bitri
    @155
    @150
    @169
    @154
    @155
    @150
    @168
    vw
    @150
    @143
    @24
    @59
    wcel
    #
    wn
    #
    vs
    @21
    wral
    #
    @155
    @167
    @149
    @143
    @177
    wi
    vy
    vw
    vy
    vw
    weq
    #
    @138
    @143
    @148
    @177
    @28
    @24
    @133
    eleq2
    #
    @178
    @147
    @176
    vs
    @21
    @178
    @139
    @175
    @28
    @24
    @59
    eleq1
    notbid
    ralbidv
    imbi12d
    spv
    @176
    @167
    vs
    @157
    @21
    @163
    @175
    @166
    @163
    @59
    @158
    @24
    @164
    eleq2d
    notbid
    rspcv
    syl9r
    alrimdv
    imim1d
    syl5bi
    a1dd
    syl9r
    syld
    com14
    imp31
    com23
    ralrimdv
    vz
    @133
    @21
    vv
    vex
    elint2
    syl6ibr
    @26
    @143
    @153
    wb
    @63
    @134
    @24
    @25
    @133
    eleq2
    ad2antrr
    sylibrd
    syl5bi
    orrd
    ex
    @144
    @138
    @140
    @178
    wo
    #
    wa
    #
    vy
    wex
    #
    @135
    @142
    @182
    @143
    @141
    @181
    vy
    @140
    @180
    @138
    @140
    @178
    orc
    anim2i
    eximi
    @143
    @138
    @178
    wa
    #
    vy
    wex
    #
    @182
    @143
    vw
    vw
    weq
    #
    @184
    vw
    equid
    @183
    @143
    @185
    wa
    vy
    @24
    vw
    vex
    @178
    @138
    @143
    @178
    @185
    @179
    vy
    vw
    vw
    equequ1
    anbi12d
    spcev
    mpan2
    @183
    @181
    vy
    @178
    @180
    @138
    @178
    @140
    olc
    anim2i
    eximi
    syl
    jaoi
    @135
    @138
    @28
    @116
    wcel
    #
    wa
    #
    vy
    wex
    @182
    vy
    @133
    @116
    eluni
    @187
    @181
    vy
    @186
    @180
    @138
    @186
    @28
    @114
    wcel
    #
    @28
    @115
    wcel
    #
    wo
    @180
    @28
    @114
    @115
    elun
    @188
    @140
    @189
    @178
    vs
    @28
    @21
    @59
    eliun
    vy
    @24
    velsn
    orbi12i
    bitri
    anbi2i
    exbii
    bitr2i
    sylib
    syl6
    adantll
    adantlr
    adantlr
    ad2ant2l
    ssrdv
    @113
    @133
    cX
    wss
    #
    vv
    @116
    wral
    @118
    cX
    wss
    @113
    @190
    vv
    @116
    @133
    @116
    wcel
    #
    @133
    @59
    wcel
    #
    vs
    @21
    wrex
    #
    vv
    vw
    weq
    #
    wo
    #
    @113
    @190
    @191
    @133
    @114
    wcel
    #
    @133
    @115
    wcel
    #
    wo
    @195
    @133
    @114
    @115
    elun
    @196
    @193
    @197
    @194
    vs
    @133
    @21
    @59
    eliun
    vv
    @24
    velsn
    orbi12i
    bitri
    @113
    @193
    @190
    @194
    @63
    @193
    @190
    wi
    @45
    @58
    @63
    @192
    @190
    vs
    @21
    @62
    vs
    @21
    nfra1
    @190
    vs
    nfv
    @63
    @66
    @62
    @192
    @190
    wi
    @62
    vs
    @21
    rsp
    @62
    @61
    cX
    wss
    #
    @192
    @133
    @61
    wss
    #
    @190
    @61
    cX
    eqimss2
    @192
    @133
    @60
    wss
    @199
    @133
    @59
    elssuni
    @133
    @60
    @34
    ssun3
    syl
    @199
    @198
    @190
    @133
    @61
    cX
    sstr
    expcom
    syl2im
    syl6
    rexlimd
    ad2antll
    @113
    @190
    @194
    @24
    cX
    wss
    @113
    @24
    @101
    cX
    @113
    @24
    @1
    wcel
    @24
    @101
    wss
    @113
    @11
    @1
    @24
    @43
    @11
    @1
    wss
    #
    @44
    @64
    @12
    @200
    @10
    @13
    @11
    @1
    elpwi
    ad2antrl
    ad2antrr
    @130
    sseldd
    @24
    @1
    elssuni
    syl
    @10
    @101
    cX
    wceq
    #
    @42
    @44
    @64
    @3
    @6
    @201
    @9
    @3
    @101
    @99
    cX
    @3
    @99
    @100
    @101
    @107
    @102
    @103
    @104
    @105
    ax-mp
    syl6req
    alexsubALT.1
    syl6eqr
    3ad2ant1
    ad3antrrr
    sseqtrd
    @133
    @24
    cX
    sseq1
    syl5ibrcom
    jaod
    syl5bi
    ralrimiv
    vv
    @116
    cX
    unissb
    sylibr
    eqssd
    @16
    @119
    vb
    @116
    @18
    @14
    @116
    wceq
    @15
    @118
    cX
    @14
    @116
    unieq
    eqeq2d
    rspcev
    syl2anc
    ex
    exlimdv
    3syld
    syl5bi
    @16
    vb
    @18
    dfrex2
    syl6ib
    con4d
    exp32
    com24
    exp32
    imp45
    imp31
end
