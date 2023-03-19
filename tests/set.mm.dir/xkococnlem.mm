include "cima.mm"
include "crest.mm"
include "co.mm"
include "cuni.mm"
include "cv.mm"
include "wceq.mm"
include "ccnv.mm"
include "cpw.mm"
include "wf.mm"
include "cfv.mm"
include "cnt.mm"
include "wss.mm"
include "ccmp.mm"
include "wcel.mm"
include "wa.mm"
include "wral.mm"
include "wex.mm"
include "cfn.mm"
include "cin.mm"
include "wrex.mm"
include "cop.mm"
include "ccn.mm"
include "crab.mm"
include "cxko.mm"
include "ctx.mm"
include "wel.mm"
include "imacmp.mm"
include "syl2anc.mm"
include "w3a.mm"
include "cnlly.mm"
include "adantr.mm"
include "cnima.mm"
include "ccom.mm"
include "imaco.mm"
include "syl5eqssr.mm"
include "wfun.mm"
include "cdm.mm"
include "wb.mm"
include "eqid.mm"
include "cnf.mm"
include "ffun.mm"
include "3syl.mm"
include "crn.mm"
include "imassrn.mm"
include "frn.mm"
include "syl5ss.mm"
include "fdm.mm"
include "sseqtr4d.mm"
include "funimass3.mm"
include "mpbid.mm"
include "sselda.mm"
include "nlly2i.mm"
include "syl3anc.mm"
include "ctop.mm"
include "cvv.mm"
include "nllytop.mm"
include "syl.mm"
include "ad3antrrr.mm"
include "imaexg.mm"
include "simprl.mm"
include "elrestr.mm"
include "simprr1.mm"
include "simpllr.mm"
include "elind.mm"
include "inss1.mm"
include "elpwi.mm"
include "ad2antlr.mm"
include "elssuni.mm"
include "sstrd.mm"
include "simprr2.mm"
include "ssntr.mm"
include "syl22anc.mm"
include "simprr3.mm"
include "jca.mm"
include "eleq2.mm"
include "sseq1.mm"
include "anbi1d.mm"
include "anbi12d.mm"
include "rspcev.mm"
include "syl12anc.mm"
include "rexlimdvaa.mm"
include "reximdva.mm"
include "mpd.mm"
include "rexcom.mm"
include "r19.42v.mm"
include "rexbii.mm"
include "bitri.mm"
include "sylib.mm"
include "ralrimiva.mm"
include "restuni.mm"
include "raleqdv.mm"
include "fveq2.mm"
include "sseq2d.mm"
include "oveq2.mm"
include "eleq1d.mm"
include "cmpcovf.mm"
include "wi.mm"
include "eqeq1d.mm"
include "biimpar.mm"
include "ciun.mm"
include "cxp.mm"
include "ad2antrr.mm"
include "cntop2.mm"
include "xkotop.mm"
include "cntop1.mm"
include "simprrl.mm"
include "sspwuni.mm"
include "wfn.mm"
include "ffn.mm"
include "fniunfv.mm"
include "oveq2d.mm"
include "inss2.mm"
include "simplr.mm"
include "sseldi.mm"
include "simprrr.mm"
include "simpr.mm"
include "ralimi.mm"
include "fiuncmp.mm"
include "eqeltrrd.mm"
include "xkoopn.mm"
include "eqsstrd.mm"
include "iunss.mm"
include "ntropn.mm"
include "ex.mm"
include "ralimdv.mm"
include "sylc.mm"
include "iunopn.mm"
include "txopn.mm"
include "imaiun.mm"
include "imaeq2d.mm"
include "syl5eqr.mm"
include "simpl1.mm"
include "3ad2ant2.mm"
include "simp3.mm"
include "r19.21bi.mm"
include "ralbidva.mm"
include "3bitr4g.mm"
include "mpbird.mm"
include "eqsstr3d.mm"
include "imaeq1.mm"
include "sseq1d.mm"
include "elrab.mm"
include "sylanbrc.mm"
include "uniiun.mm"
include "syl6eq.mm"
include "simpl.mm"
include "ss2iun.mm"
include "opelxpi.mm"
include "anbi12i.mm"
include "simprll.mm"
include "coeq1.mm"
include "coeq2.mm"
include "vex.mm"
include "coex.mm"
include "ovmpt2.mm"
include "cnco.mm"
include "ntrss2.mm"
include "sseqtrd.mm"
include "imass2.mm"
include "simprlr.mm"
include "syl5eqss.mm"
include "eqeltrd.mm"
include "sylan2b.mm"
include "ralrimivva.mm"
include "mpt2fun.mm"
include "ssrab2.mm"
include "xpss12.mm"
include "mp2an.mm"
include "dmmpt2.mm"
include "sseqtr4i.mm"
include "funimassov.mm"
include "sylibr.mm"
include "expr.mm"
include "exlimdv.mm"
include "syldan.mm"
include "expimpd.mm"
include "rexlimdva.mm"

theorem xkococnlem
  let wph: wff ph
  let vz: setvar z
  let cA: class A
  let cB: class B
  let cR: class R
  let cS: class S
  let cT: class T
  let vf: setvar f
  let vg: setvar g
  let vh: setvar h
  let cF: class F
  let cK: class K
  let cV: class V
  let va: setvar a
  let vk: setvar k
  let vs: setvar s
  let vu: setvar u
  let vv: setvar v
  let vw: setvar w
  let vx: setvar x
  let vy: setvar y
  let vb: setvar b
  assume xkococn.1: |- F = ( f e. ( S Cn T ) , g e. ( R Cn S ) |-> ( f o. g ) )
  assume xkococn.s: |- ( ph -> S e. N-Locally Comp )
  assume xkococn.k: |- ( ph -> K C_ U. R )
  assume xkococn.c: |- ( ph -> ( R |`t K ) e. Comp )
  assume xkococn.v: |- ( ph -> V e. T )
  assume xkococn.a: |- ( ph -> A e. ( S Cn T ) )
  assume xkococn.b: |- ( ph -> B e. ( R Cn S ) )
  assume xkococn.i: |- ( ph -> ( ( A o. B ) " K ) C_ V )

  disjoint A z
  disjoint B z
  disjoint f g
  disjoint f h
  disjoint f z
  disjoint R f
  disjoint g h
  disjoint g z
  disjoint R g
  disjoint h z
  disjoint R h
  disjoint R z
  disjoint S f
  disjoint S g
  disjoint S z
  disjoint K h
  disjoint K z
  disjoint T f
  disjoint T g
  disjoint T h
  disjoint T z
  disjoint F z
  disjoint V h
  disjoint V z
  disjoint a k
  disjoint a s
  disjoint a u
  disjoint a v
  disjoint a w
  disjoint a x
  disjoint a y
  disjoint a z
  disjoint A a
  disjoint k s
  disjoint k u
  disjoint k v
  disjoint k w
  disjoint k x
  disjoint k y
  disjoint k z
  disjoint A k
  disjoint s u
  disjoint s v
  disjoint s w
  disjoint s x
  disjoint s y
  disjoint s z
  disjoint A s
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
  disjoint x z
  disjoint A x
  disjoint y z
  disjoint A y
  disjoint b k
  disjoint b s
  disjoint b u
  disjoint b v
  disjoint b w
  disjoint b x
  disjoint b y
  disjoint b z
  disjoint B b
  disjoint B k
  disjoint B s
  disjoint B u
  disjoint B v
  disjoint B w
  disjoint B x
  disjoint B y
  disjoint k ph
  disjoint ph s
  disjoint ph u
  disjoint ph v
  disjoint ph w
  disjoint ph x
  disjoint a b
  disjoint a f
  disjoint a g
  disjoint a h
  disjoint R a
  disjoint b f
  disjoint b g
  disjoint b h
  disjoint R b
  disjoint f k
  disjoint f u
  disjoint f v
  disjoint f w
  disjoint f x
  disjoint f y
  disjoint g k
  disjoint g u
  disjoint g v
  disjoint g w
  disjoint g x
  disjoint g y
  disjoint h k
  disjoint h u
  disjoint h v
  disjoint h w
  disjoint h x
  disjoint h y
  disjoint R k
  disjoint R u
  disjoint R v
  disjoint R w
  disjoint R x
  disjoint R y
  disjoint S a
  disjoint S b
  disjoint f s
  disjoint g s
  disjoint S k
  disjoint S s
  disjoint S u
  disjoint S v
  disjoint S w
  disjoint S x
  disjoint S y
  disjoint K b
  disjoint h s
  disjoint K k
  disjoint K s
  disjoint K u
  disjoint K v
  disjoint K w
  disjoint K x
  disjoint K y
  disjoint T a
  disjoint T b
  disjoint T k
  disjoint T u
  disjoint T v
  disjoint T w
  disjoint T x
  disjoint T y
  disjoint F a
  disjoint F b
  disjoint F k
  disjoint F u
  disjoint F v
  disjoint F w
  disjoint F x
  disjoint F y
  disjoint V a
  disjoint V k
  disjoint V s
  disjoint V u
  disjoint V v
  disjoint V w
  disjoint V x
  disjoint V y
  assert |- ( ph -> E. z e. ( ( T ^ko S ) tX ( S ^ko R ) ) ( <. A , B >. e. z /\ z C_ ( `' F " { h e. ( R Cn T ) | ( h " K ) C_ V } ) ) )

  proof
    wph
    cS
    cB
    cK
    cima
    #
    crest
    co
    #
    cuni
    #
    vw
    cv
    #
    cuni
    #
    wceq
    #
    @3
    cA
    ccnv
    cV
    cima
    #
    cpw
    #
    vk
    cv
    #
    wf
    #
    vy
    cv
    #
    @10
    @8
    cfv
    #
    cS
    cnt
    cfv
    #
    cfv
    #
    wss
    #
    cS
    @11
    crest
    co
    #
    ccmp
    wcel
    #
    wa
    #
    vy
    @3
    wral
    #
    wa
    #
    vk
    wex
    #
    wa
    #
    vw
    @1
    cpw
    #
    cfn
    cin
    #
    wrex
    #
    cA
    cB
    cop
    #
    vz
    cv
    #
    wcel
    #
    @26
    cF
    ccnv
    vh
    cv
    #
    cK
    cima
    #
    cV
    wss
    #
    vh
    cR
    cT
    ccn
    co
    #
    crab
    #
    cima
    #
    wss
    #
    wa
    #
    vz
    cT
    cS
    cxko
    co
    #
    cS
    cR
    cxko
    co
    #
    ctx
    co
    #
    wrex
    #
    wph
    @1
    ccmp
    wcel
    #
    vx
    vy
    wel
    #
    @10
    vs
    cv
    #
    @12
    cfv
    #
    wss
    #
    cS
    @42
    crest
    co
    #
    ccmp
    wcel
    #
    wa
    #
    vs
    @7
    wrex
    wa
    #
    vy
    @1
    wrex
    #
    vx
    @2
    wral
    #
    @24
    wph
    cB
    cR
    cS
    ccn
    co
    #
    wcel
    #
    cR
    cK
    crest
    co
    ccmp
    wcel
    #
    @40
    xkococn.b
    xkococn.c
    cK
    cB
    cR
    cS
    imacmp
    syl2anc
    wph
    @49
    vx
    @0
    wral
    @50
    wph
    @49
    vx
    @0
    wph
    vx
    cv
    #
    @0
    wcel
    #
    wa
    #
    @41
    @47
    wa
    #
    vy
    @1
    wrex
    #
    vs
    @7
    wrex
    #
    @49
    @56
    vx
    vu
    wel
    #
    vu
    cv
    #
    @42
    wss
    #
    @46
    w3a
    #
    vu
    cS
    wrex
    #
    vs
    @7
    wrex
    #
    @59
    @56
    cS
    ccmp
    cnlly
    wcel
    #
    @6
    cS
    wcel
    #
    @54
    @6
    wcel
    @65
    wph
    @66
    @55
    xkococn.s
    adantr
    wph
    @67
    @55
    wph
    cA
    cS
    cT
    ccn
    co
    #
    wcel
    #
    cV
    cT
    wcel
    #
    @67
    xkococn.a
    xkococn.v
    cV
    cA
    cS
    cT
    cnima
    syl2anc
    #
    adantr
    wph
    @0
    @6
    @54
    wph
    cA
    @0
    cima
    #
    cV
    wss
    #
    @0
    @6
    wss
    #
    wph
    @72
    cA
    cB
    ccom
    cK
    cima
    cV
    cA
    cB
    cK
    imaco
    xkococn.i
    syl5eqssr
    wph
    cA
    wfun
    #
    @0
    cA
    cdm
    #
    wss
    @73
    @74
    wb
    wph
    @69
    cS
    cuni
    #
    cT
    cuni
    #
    cA
    wf
    #
    @75
    xkococn.a
    cA
    cS
    cT
    @77
    @78
    @77
    eqid
    #
    @78
    eqid
    cnf
    #
    @77
    @78
    cA
    ffun
    3syl
    #
    wph
    @0
    @77
    @76
    wph
    @0
    cB
    crn
    #
    @77
    cB
    cK
    imassrn
    wph
    @52
    cR
    cuni
    #
    @77
    cB
    wf
    @83
    @77
    wss
    xkococn.b
    cB
    cR
    cS
    @84
    @77
    @84
    eqid
    #
    @80
    cnf
    @84
    @77
    cB
    frn
    3syl
    syl5ss
    #
    wph
    @69
    @79
    @76
    @77
    wceq
    #
    xkococn.a
    @81
    @77
    @78
    cA
    fdm
    3syl
    #
    sseqtr4d
    @0
    cV
    cA
    funimass3
    syl2anc
    mpbid
    sselda
    vu
    ccmp
    @54
    @6
    cS
    vs
    nlly2i
    syl3anc
    @56
    @64
    @58
    vs
    @7
    @56
    @42
    @7
    wcel
    #
    wa
    #
    @63
    @58
    vu
    cS
    @90
    @61
    cS
    wcel
    #
    @63
    wa
    #
    wa
    #
    @61
    @0
    cin
    #
    @1
    wcel
    #
    @54
    @94
    wcel
    #
    @94
    @43
    wss
    #
    @46
    wa
    #
    @58
    @93
    cS
    ctop
    wcel
    #
    @0
    cvv
    wcel
    #
    @91
    @95
    wph
    @99
    @55
    @89
    @92
    wph
    @66
    @99
    xkococn.s
    ccmp
    cS
    nllytop
    syl
    #
    ad3antrrr
    #
    wph
    @100
    @55
    @89
    @92
    wph
    @52
    @100
    xkococn.b
    cB
    cK
    @51
    imaexg
    syl
    ad3antrrr
    @90
    @91
    @63
    simprl
    #
    @61
    @0
    cS
    ctop
    cvv
    elrestr
    syl3anc
    @93
    @61
    @0
    @54
    @60
    @62
    @46
    @91
    @90
    simprr1
    wph
    @55
    @89
    @92
    simpllr
    elind
    @93
    @97
    @46
    @93
    @94
    @61
    @43
    @61
    @0
    inss1
    @93
    @99
    @42
    @77
    wss
    @91
    @62
    @61
    @43
    wss
    @102
    @93
    @42
    @6
    @77
    @89
    @42
    @6
    wss
    @56
    @92
    @42
    @6
    elpwi
    ad2antlr
    wph
    @6
    @77
    wss
    #
    @55
    @89
    @92
    wph
    @67
    @104
    @71
    @6
    cS
    elssuni
    #
    syl
    ad3antrrr
    sstrd
    @103
    @60
    @62
    @46
    @91
    @90
    simprr2
    @42
    cS
    @61
    @77
    @80
    ssntr
    syl22anc
    syl5ss
    @60
    @62
    @46
    @91
    @90
    simprr3
    jca
    @57
    @96
    @98
    wa
    vy
    @94
    @1
    @10
    @94
    wceq
    #
    @41
    @96
    @47
    @98
    @10
    @94
    @54
    eleq2
    @106
    @44
    @97
    @46
    @10
    @94
    @43
    sseq1
    anbi1d
    anbi12d
    rspcev
    syl12anc
    rexlimdvaa
    reximdva
    mpd
    @59
    @57
    vs
    @7
    wrex
    #
    vy
    @1
    wrex
    @49
    @57
    vs
    vy
    @7
    @1
    rexcom
    @107
    @48
    vy
    @1
    @41
    @47
    vs
    @7
    r19.42v
    rexbii
    bitri
    sylib
    ralrimiva
    wph
    @49
    vx
    @0
    @2
    wph
    @99
    @0
    @77
    wss
    @0
    @2
    wceq
    #
    @101
    @86
    @0
    cS
    @77
    @80
    restuni
    syl2anc
    #
    raleqdv
    mpbid
    @47
    @17
    vx
    vy
    vs
    @7
    vk
    @1
    @2
    vw
    @2
    eqid
    @42
    @11
    wceq
    #
    @44
    @14
    @46
    @16
    @110
    @43
    @13
    @10
    @42
    @11
    @12
    fveq2
    sseq2d
    @110
    @45
    @15
    ccmp
    @42
    @11
    cS
    crest
    oveq2
    eleq1d
    anbi12d
    cmpcovf
    syl2anc
    wph
    @21
    @39
    vw
    @23
    wph
    @3
    @23
    wcel
    #
    wa
    #
    @5
    @20
    @39
    @112
    @5
    @0
    @4
    wceq
    #
    @20
    @39
    wi
    @112
    @113
    @5
    @112
    @0
    @2
    @4
    wph
    @108
    @111
    @109
    adantr
    eqeq1d
    biimpar
    @112
    @113
    wa
    @19
    @39
    vk
    @112
    @113
    @19
    @39
    @112
    @113
    @19
    wa
    #
    wa
    #
    va
    cv
    #
    @8
    crn
    #
    cuni
    #
    cima
    #
    cV
    wss
    #
    va
    @68
    crab
    #
    vb
    cv
    #
    cK
    cima
    #
    vy
    @3
    @13
    ciun
    #
    wss
    #
    vb
    @51
    crab
    #
    cxp
    #
    @38
    wcel
    #
    @25
    @127
    wcel
    #
    @127
    @33
    wss
    #
    @39
    @115
    @36
    ctop
    wcel
    #
    @37
    ctop
    wcel
    #
    @121
    @36
    wcel
    @126
    @37
    wcel
    @128
    @115
    @99
    cT
    ctop
    wcel
    #
    @131
    wph
    @99
    @111
    @114
    @101
    ad2antrr
    #
    wph
    @133
    @111
    @114
    wph
    @69
    @133
    xkococn.a
    cA
    cS
    cT
    cntop2
    syl
    ad2antrr
    #
    cS
    cT
    xkotop
    syl2anc
    @115
    cR
    ctop
    wcel
    #
    @99
    @132
    wph
    @136
    @111
    @114
    wph
    @52
    @136
    xkococn.b
    cB
    cR
    cS
    cntop1
    syl
    ad2antrr
    #
    @134
    cR
    cS
    xkotop
    syl2anc
    @115
    @118
    cS
    cT
    cV
    va
    @77
    @80
    @134
    @135
    @115
    @118
    @6
    @77
    @115
    @117
    @7
    wss
    #
    @118
    @6
    wss
    @115
    @9
    @138
    @112
    @113
    @9
    @18
    simprrl
    #
    @3
    @7
    @8
    frn
    syl
    @117
    @6
    sspwuni
    sylib
    #
    @115
    @67
    @104
    wph
    @67
    @111
    @114
    @71
    ad2antrr
    @105
    syl
    sstrd
    #
    @115
    cS
    vy
    @3
    @11
    ciun
    #
    crest
    co
    #
    cS
    @118
    crest
    co
    ccmp
    @115
    @142
    @118
    cS
    crest
    @115
    @9
    @8
    @3
    wfn
    #
    @142
    @118
    wceq
    #
    @139
    @3
    @7
    @8
    ffn
    #
    vy
    @3
    @8
    fniunfv
    #
    3syl
    #
    oveq2d
    @115
    @99
    @3
    cfn
    wcel
    @16
    vy
    @3
    wral
    #
    @143
    ccmp
    wcel
    @134
    @115
    @23
    cfn
    @3
    @22
    cfn
    inss2
    wph
    @111
    @114
    simplr
    sseldi
    @115
    @18
    @149
    @112
    @113
    @9
    @18
    simprrr
    #
    @17
    @16
    vy
    @3
    @14
    @16
    simpr
    ralimi
    syl
    vy
    @3
    @11
    cS
    @77
    @80
    fiuncmp
    syl3anc
    eqeltrrd
    wph
    @70
    @111
    @114
    xkococn.v
    ad2antrr
    xkoopn
    @115
    cK
    cR
    cS
    @124
    vb
    @84
    @85
    @137
    @134
    wph
    cK
    @84
    wss
    @111
    @114
    xkococn.k
    ad2antrr
    wph
    @53
    @111
    @114
    xkococn.c
    ad2antrr
    @115
    @99
    @13
    cS
    wcel
    #
    vy
    @3
    wral
    #
    @124
    cS
    wcel
    @134
    @115
    @99
    @11
    @77
    wss
    #
    vy
    @3
    wral
    #
    @152
    @134
    @115
    @142
    @77
    wss
    @154
    @115
    @142
    @118
    @77
    @148
    @141
    eqsstrd
    vy
    @3
    @11
    @77
    iunss
    sylib
    #
    @99
    @153
    @151
    vy
    @3
    @99
    @153
    @151
    @11
    cS
    @77
    @80
    ntropn
    ex
    ralimdv
    sylc
    vy
    @3
    @13
    cS
    iunopn
    syl2anc
    xkoopn
    @121
    @126
    @36
    @37
    ctop
    ctop
    txopn
    syl22anc
    @115
    cA
    @121
    wcel
    #
    cB
    @126
    wcel
    #
    @129
    @115
    @69
    cA
    @118
    cima
    #
    cV
    wss
    #
    @156
    wph
    @69
    @111
    @114
    xkococn.a
    ad2antrr
    @115
    @158
    vy
    @3
    cA
    @11
    cima
    #
    ciun
    #
    cV
    @115
    @161
    cA
    @142
    cima
    @158
    vy
    cA
    @3
    @11
    imaiun
    @115
    @142
    @118
    cA
    @148
    imaeq2d
    syl5eqr
    @115
    @161
    cV
    wss
    #
    @142
    @6
    wss
    #
    @115
    @142
    @118
    @6
    @148
    @140
    eqsstrd
    @115
    @75
    @144
    @118
    @76
    wss
    #
    @162
    @163
    wb
    wph
    @75
    @111
    @114
    @82
    ad2antrr
    @115
    @9
    @144
    @139
    @146
    syl
    @115
    @118
    @77
    @76
    @141
    wph
    @87
    @111
    @114
    @88
    ad2antrr
    sseqtr4d
    @75
    @144
    @164
    w3a
    #
    @160
    cV
    wss
    #
    vy
    @3
    wral
    @11
    @6
    wss
    #
    vy
    @3
    wral
    @162
    @163
    @165
    @166
    @167
    vy
    @3
    @165
    vy
    vw
    wel
    #
    wa
    @75
    @11
    @76
    wss
    #
    @166
    @167
    wb
    @75
    @144
    @164
    @168
    simpl1
    @165
    @169
    vy
    @3
    @165
    @142
    @76
    wss
    @169
    vy
    @3
    wral
    @165
    @142
    @118
    @76
    @144
    @75
    @145
    @164
    @147
    3ad2ant2
    @75
    @144
    @164
    simp3
    eqsstrd
    vy
    @3
    @11
    @76
    iunss
    sylib
    r19.21bi
    @11
    cV
    cA
    funimass3
    syl2anc
    ralbidva
    vy
    @3
    @160
    cV
    iunss
    vy
    @3
    @11
    @6
    iunss
    3bitr4g
    syl3anc
    mpbird
    eqsstr3d
    @120
    @159
    va
    cA
    @68
    @116
    cA
    wceq
    @119
    @158
    cV
    @116
    cA
    @118
    imaeq1
    sseq1d
    elrab
    sylanbrc
    @115
    @52
    @0
    @124
    wss
    #
    @157
    wph
    @52
    @111
    @114
    xkococn.b
    ad2antrr
    @115
    @0
    vy
    @3
    @10
    ciun
    #
    @124
    @115
    @0
    @4
    @171
    @112
    @113
    @19
    simprl
    vy
    @3
    uniiun
    syl6eq
    @115
    @18
    @14
    vy
    @3
    wral
    @171
    @124
    wss
    @150
    @17
    @14
    vy
    @3
    @14
    @16
    simpl
    ralimi
    vy
    @3
    @10
    @13
    ss2iun
    3syl
    eqsstrd
    @125
    @170
    vb
    cB
    @51
    @122
    cB
    wceq
    @123
    @0
    @124
    @122
    cB
    cK
    imaeq1
    sseq1d
    elrab
    sylanbrc
    cA
    cB
    @121
    @126
    opelxpi
    syl2anc
    @115
    cF
    @127
    cima
    @32
    wss
    #
    @130
    @115
    @61
    vv
    cv
    #
    cF
    co
    #
    @32
    wcel
    #
    vv
    @126
    wral
    vu
    @121
    wral
    #
    @172
    @115
    @175
    vu
    vv
    @121
    @126
    @61
    @121
    wcel
    #
    @173
    @126
    wcel
    #
    wa
    @115
    @61
    @68
    wcel
    #
    @61
    @118
    cima
    #
    cV
    wss
    #
    wa
    #
    @173
    @51
    wcel
    #
    @173
    cK
    cima
    #
    @124
    wss
    #
    wa
    #
    wa
    #
    @175
    @177
    @182
    @178
    @186
    @120
    @181
    va
    @61
    @68
    @116
    @61
    wceq
    @119
    @180
    cV
    @116
    @61
    @118
    imaeq1
    sseq1d
    elrab
    @125
    @185
    vb
    @173
    @51
    @122
    @173
    wceq
    @123
    @184
    @124
    @122
    @173
    cK
    imaeq1
    sseq1d
    elrab
    anbi12i
    @115
    @187
    wa
    #
    @174
    @61
    @173
    ccom
    #
    @32
    @188
    @179
    @183
    @174
    @189
    wceq
    @115
    @179
    @181
    @186
    simprll
    #
    @115
    @182
    @183
    @185
    simprrl
    #
    vf
    vg
    @61
    @173
    @68
    @51
    vf
    cv
    #
    vg
    cv
    #
    ccom
    #
    @189
    cF
    @61
    @193
    ccom
    @192
    @61
    @193
    coeq1
    @193
    @173
    @61
    coeq2
    xkococn.1
    @61
    @173
    vu
    vex
    vv
    vex
    coex
    ovmpt2
    syl2anc
    @188
    @189
    @31
    wcel
    #
    @189
    cK
    cima
    #
    cV
    wss
    #
    @189
    @32
    wcel
    @188
    @183
    @179
    @195
    @191
    @190
    @173
    @61
    cR
    cS
    cT
    cnco
    syl2anc
    @188
    @196
    @61
    @184
    cima
    #
    cV
    @61
    @173
    cK
    imaco
    @188
    @198
    @180
    cV
    @188
    @184
    @118
    wss
    @198
    @180
    wss
    @188
    @184
    @124
    @118
    @115
    @182
    @183
    @185
    simprrr
    @115
    @124
    @118
    wss
    @187
    @115
    @124
    @142
    @118
    @115
    @13
    @11
    wss
    #
    vy
    @3
    wral
    #
    @124
    @142
    wss
    @115
    @99
    @154
    @200
    @134
    @155
    @99
    @153
    @199
    vy
    @3
    @99
    @153
    @199
    @11
    cS
    @77
    @80
    ntrss2
    ex
    ralimdv
    sylc
    vy
    @3
    @13
    @11
    ss2iun
    syl
    @148
    sseqtrd
    adantr
    sstrd
    @184
    @118
    @61
    imass2
    syl
    @115
    @179
    @181
    @186
    simprlr
    sstrd
    syl5eqss
    @30
    @197
    vh
    @189
    @31
    @28
    @189
    wceq
    @29
    @196
    cV
    @28
    @189
    cK
    imaeq1
    sseq1d
    elrab
    sylanbrc
    eqeltrd
    sylan2b
    ralrimivva
    cF
    wfun
    #
    @127
    cF
    cdm
    #
    wss
    #
    @172
    @176
    wb
    vf
    vg
    @68
    @51
    @194
    cF
    xkococn.1
    mpt2fun
    #
    @127
    @68
    @51
    cxp
    #
    @202
    @121
    @68
    wss
    @126
    @51
    wss
    @127
    @205
    wss
    @120
    va
    @68
    ssrab2
    @125
    vb
    @51
    ssrab2
    @121
    @68
    @126
    @51
    xpss12
    mp2an
    vf
    vg
    @68
    @51
    @194
    cF
    xkococn.1
    @192
    @193
    vf
    vex
    vg
    vex
    coex
    dmmpt2
    sseqtr4i
    #
    vu
    vv
    @121
    @126
    @32
    cF
    funimassov
    mp2an
    sylibr
    @201
    @203
    @172
    @130
    wb
    @204
    @206
    @127
    @32
    cF
    funimass3
    mp2an
    sylib
    @35
    @129
    @130
    wa
    vz
    @127
    @38
    @26
    @127
    wceq
    @27
    @129
    @34
    @130
    @26
    @127
    @25
    eleq2
    @26
    @127
    @33
    sseq1
    anbi12d
    rspcev
    syl12anc
    expr
    exlimdv
    syldan
    expimpd
    rexlimdva
    mpd
end
