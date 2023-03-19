include "cv.mm"
include "wne.mm"
include "wrex.mm"
include "wrmo.mm"
include "wreu.mm"
include "poimirlem17.mm"
include "c2nd.mm"
include "cfv.mm"
include "wceq.mm"
include "wi.mm"
include "wral.mm"
include "wcel.mm"
include "wa.mm"
include "wn.mm"
include "cc0.mm"
include "c1.mm"
include "cmin.mm"
include "co.mm"
include "cfz.mm"
include "adantr.mm"
include "cn.mm"
include "0nnn.mm"
include "elfznn.mm"
include "mto.mm"
include "eleq1.mm"
include "mtbiri.mm"
include "necon2ai.mm"
include "c1st.mm"
include "ad2antrr.mm"
include "clt.mm"
include "wbr.mm"
include "caddc.mm"
include "cif.mm"
include "cima.mm"
include "csn.mm"
include "cxp.mm"
include "cun.mm"
include "cof.mm"
include "csb.mm"
include "cmpt.mm"
include "cfzo.mm"
include "cmap.mm"
include "wf1o.mm"
include "cab.mm"
include "weq.mm"
include "fveq2.mm"
include "breq2d.mm"
include "ifbid.mm"
include "csbeq1d.mm"
include "fveq2d.mm"
include "imaeq1d.mm"
include "xpeq1d.mm"
include "uneq12d.mm"
include "oveq12d.mm"
include "csbeq2dv.mm"
include "eqtrd.mm"
include "mpteq2dv.mm"
include "eqeq2d.mm"
include "elrab2.mm"
include "simprbi.mm"
include "ad2antlr.mm"
include "cz.mm"
include "wf.mm"
include "wss.mm"
include "crab.mm"
include "elrabi.mm"
include "eleq2s.mm"
include "xp1st.mm"
include "syl.mm"
include "elmapi.mm"
include "elfzoelz.mm"
include "ssriv.mm"
include "fss.mm"
include "sylancl.mm"
include "xp2nd.mm"
include "fvex.mm"
include "f1oeq1.mm"
include "elab.mm"
include "sylib.mm"
include "simpr.mm"
include "poimirlem1.mm"
include "simplr.mm"
include "cdif.mm"
include "eldifsn.mm"
include "biimpri.mm"
include "sylan.mm"
include "poimirlem2.mm"
include "ex.mm"
include "necon1bd.mm"
include "adantlr.mm"
include "mpd.mm"
include "neeq1d.mm"
include "exbiri.mm"
include "mpdi.mm"
include "necon2bd.mm"
include "cuz.mm"
include "cc.mm"
include "nncnd.mm"
include "npcan1.mm"
include "nnuz.mm"
include "syl6eleq.mm"
include "eqeltrd.mm"
include "nnzd.mm"
include "peano2zm.mm"
include "uzid.mm"
include "peano2uz.mm"
include "3syl.mm"
include "eqeltrrd.mm"
include "fzsplit2.mm"
include "syl2anc.mm"
include "oveq1d.mm"
include "fzsn.mm"
include "uneq2d.mm"
include "eleq2d.mm"
include "notbid.mm"
include "wo.mm"
include "ioran.mm"
include "elun.mm"
include "elsn.mm"
include "orbi2i.mm"
include "bitri.mm"
include "xchnxbir.mm"
include "syl6bb.mm"
include "anbi2d.mm"
include "cn0.mm"
include "nnnn0d.mm"
include "nn0uz.mm"
include "fzpred.mm"
include "difeq1d.mm"
include "difun2.mm"
include "0p1e1.mm"
include "oveq1i.mm"
include "uneq2i.mm"
include "difeq1i.mm"
include "cin.mm"
include "c0.mm"
include "incom.mm"
include "disjsn.mm"
include "mpbir.mm"
include "eqtri.mm"
include "disj3.mm"
include "mpbi.mm"
include "3eqtr4i.mm"
include "syl6eq.mm"
include "eldif.mm"
include "3bitr3g.mm"
include "bitr3d.mm"
include "biimpd.mm"
include "expdimp.mm"
include "sylan2.mm"
include "mpand.mm"
include "poimirlem13.mm"
include "eqeq1d.mm"
include "rmo4.mm"
include "r19.21bi.mm"
include "eqeq2.mm"
include "imbi12d.mm"
include "rspccv.mm"
include "sylc.mm"
include "mpan2d.mm"
include "syld.mm"
include "necon1ad.mm"
include "ralrimiva.mm"
include "poimirlem14.mm"
include "rmoim.mm"
include "reu5.mm"
include "sylanbrc.mm"

theorem poimirlem18
  let wph: wff ph
  let vy: setvar y
  let vz: setvar z
  let vt: setvar t
  let cS: class S
  let cT: class T
  let vf: setvar f
  let vj: setvar j
  let vn: setvar n
  let cF: class F
  let cK: class K
  let cN: class N
  let vp: setvar p
  let vk: setvar k
  let vm: setvar m
  let vs: setvar s
  let vi: setvar i
  let vq: setvar q
  let vu: setvar u
  let vw: setvar w
  let vx: setvar x
  let cM: class M
  let cU: class U
  let cV: class V
  let cB: class B
  assume poimir.0: |- ( ph -> N e. NN )
  assume poimirlem22.s: |- S = { t e. ( ( ( ( 0 ..^ K ) ^m ( 1 ... N ) ) X. { f | f : ( 1 ... N ) -1-1-onto-> ( 1 ... N ) } ) X. ( 0 ... N ) ) | F = ( y e. ( 0 ... ( N - 1 ) ) |-> [_ if ( y < ( 2nd ` t ) , y , ( y + 1 ) ) / j ]_ ( ( 1st ` ( 1st ` t ) ) oF + ( ( ( ( 2nd ` ( 1st ` t ) ) " ( 1 ... j ) ) X. { 1 } ) u. ( ( ( 2nd ` ( 1st ` t ) ) " ( ( j + 1 ) ... N ) ) X. { 0 } ) ) ) ) }
  assume poimirlem22.1: |- ( ph -> F : ( 0 ... ( N - 1 ) ) --> ( ( 0 ... K ) ^m ( 1 ... N ) ) )
  assume poimirlem22.2: |- ( ph -> T e. S )
  assume poimirlem18.3: |- ( ( ph /\ n e. ( 1 ... N ) ) -> E. p e. ran F ( p ` n ) =/= K )
  assume poimirlem18.4: |- ( ph -> ( 2nd ` T ) = 0 )

  disjoint j n
  disjoint j p
  disjoint j t
  disjoint j y
  disjoint j z
  disjoint S j
  disjoint n p
  disjoint n t
  disjoint n y
  disjoint n z
  disjoint S n
  disjoint p t
  disjoint p y
  disjoint p z
  disjoint S p
  disjoint t y
  disjoint t z
  disjoint S t
  disjoint y z
  disjoint S y
  disjoint S z
  disjoint f j
  disjoint f n
  disjoint f p
  disjoint f t
  disjoint f y
  disjoint f z
  disjoint j n
  disjoint j p
  disjoint j t
  disjoint j y
  disjoint j z
  disjoint n p
  disjoint n t
  disjoint n y
  disjoint n z
  disjoint p t
  disjoint p y
  disjoint p z
  disjoint t y
  disjoint t z
  disjoint y z
  disjoint j ph
  disjoint n ph
  disjoint ph y
  disjoint F j
  disjoint F n
  disjoint F y
  disjoint N j
  disjoint N n
  disjoint N y
  disjoint T j
  disjoint T n
  disjoint T y
  disjoint p ph
  disjoint ph t
  disjoint K f
  disjoint K j
  disjoint K n
  disjoint K p
  disjoint K t
  disjoint N f
  disjoint N p
  disjoint N t
  disjoint T f
  disjoint T p
  disjoint ph z
  disjoint F f
  disjoint F p
  disjoint F t
  disjoint F z
  disjoint K z
  disjoint N z
  disjoint T t
  disjoint T z
  disjoint j k
  disjoint j m
  disjoint j s
  disjoint k m
  disjoint k n
  disjoint k p
  disjoint k s
  disjoint k t
  disjoint k y
  disjoint k z
  disjoint S k
  disjoint m n
  disjoint m p
  disjoint m s
  disjoint m t
  disjoint m y
  disjoint m z
  disjoint S m
  disjoint n s
  disjoint p s
  disjoint s t
  disjoint s y
  disjoint s z
  disjoint S s
  disjoint f i
  disjoint f k
  disjoint f m
  disjoint f q
  disjoint f s
  disjoint f u
  disjoint f w
  disjoint f x
  disjoint i j
  disjoint i k
  disjoint i m
  disjoint i n
  disjoint i p
  disjoint i q
  disjoint i s
  disjoint i t
  disjoint i u
  disjoint i w
  disjoint i x
  disjoint i y
  disjoint i z
  disjoint j k
  disjoint j m
  disjoint j q
  disjoint j s
  disjoint j u
  disjoint j w
  disjoint j x
  disjoint k m
  disjoint k n
  disjoint k p
  disjoint k q
  disjoint k s
  disjoint k t
  disjoint k u
  disjoint k w
  disjoint k x
  disjoint k y
  disjoint k z
  disjoint m n
  disjoint m p
  disjoint m q
  disjoint m s
  disjoint m t
  disjoint m u
  disjoint m w
  disjoint m x
  disjoint m y
  disjoint m z
  disjoint n q
  disjoint n s
  disjoint n u
  disjoint n w
  disjoint n x
  disjoint p q
  disjoint p s
  disjoint p u
  disjoint p w
  disjoint p x
  disjoint q s
  disjoint q t
  disjoint q u
  disjoint q w
  disjoint q x
  disjoint q y
  disjoint q z
  disjoint s t
  disjoint s u
  disjoint s w
  disjoint s x
  disjoint s y
  disjoint s z
  disjoint t u
  disjoint t w
  disjoint t x
  disjoint u w
  disjoint u x
  disjoint u y
  disjoint u z
  disjoint w x
  disjoint w y
  disjoint w z
  disjoint x y
  disjoint x z
  disjoint m ph
  disjoint F m
  disjoint M j
  disjoint M m
  disjoint M n
  disjoint M y
  disjoint N m
  disjoint T m
  disjoint U j
  disjoint U m
  disjoint U n
  disjoint U y
  disjoint V j
  disjoint V m
  disjoint V n
  disjoint V y
  disjoint i ph
  disjoint k ph
  disjoint ph s
  disjoint B f
  disjoint B i
  disjoint B j
  disjoint B k
  disjoint B n
  disjoint B s
  disjoint B t
  disjoint K i
  disjoint K k
  disjoint K s
  disjoint M f
  disjoint M i
  disjoint M k
  disjoint M p
  disjoint M s
  disjoint M t
  disjoint N i
  disjoint N k
  disjoint N s
  disjoint T i
  disjoint U f
  disjoint U i
  disjoint U p
  disjoint F k
  disjoint F s
  disjoint T k
  disjoint T s
  disjoint U k
  disjoint U t
  assert |- ( ph -> E! z e. S z =/= T )

  proof
    wph
    vz
    cv
    #
    cT
    wne
    #
    vz
    cS
    wrex
    @1
    vz
    cS
    wrmo
    #
    @1
    vz
    cS
    wreu
    wph
    vy
    vz
    vt
    cS
    cT
    vf
    vj
    vn
    cF
    cK
    cN
    vp
    poimir.0
    poimirlem22.s
    poimirlem22.1
    poimirlem22.2
    poimirlem18.3
    poimirlem18.4
    poimirlem17
    wph
    @1
    @0
    c2nd
    cfv
    #
    cN
    wceq
    #
    wi
    #
    vz
    cS
    wral
    @4
    vz
    cS
    wrmo
    @2
    wph
    @5
    vz
    cS
    wph
    @0
    cS
    wcel
    #
    wa
    #
    @4
    @0
    cT
    @7
    @4
    wn
    #
    @3
    cc0
    wceq
    #
    @0
    cT
    wceq
    #
    @7
    @3
    c1
    cN
    c1
    cmin
    co
    #
    cfz
    co
    #
    wcel
    #
    wn
    #
    @8
    @9
    @7
    cT
    c2nd
    cfv
    #
    cc0
    wceq
    #
    @14
    wph
    @16
    @6
    poimirlem18.4
    adantr
    #
    @7
    @13
    @15
    cc0
    @7
    @13
    @3
    cc0
    wne
    #
    @15
    cc0
    wne
    #
    @13
    @3
    cc0
    @9
    @13
    cc0
    @12
    wcel
    #
    @20
    cc0
    cn
    wcel
    #
    0nnn
    cc0
    @11
    elfznn
    mto
    @3
    cc0
    @12
    eleq1
    mtbiri
    necon2ai
    @7
    @13
    @19
    @18
    @7
    @13
    wa
    #
    @15
    @3
    cc0
    @22
    vn
    cv
    #
    @3
    c1
    cmin
    co
    cF
    cfv
    cfv
    @23
    @3
    cF
    cfv
    cfv
    wne
    vn
    c1
    cN
    cfz
    co
    #
    wrmo
    #
    wn
    #
    @15
    @3
    wceq
    #
    @22
    vy
    @0
    c1st
    cfv
    #
    c1st
    cfv
    #
    @28
    c2nd
    cfv
    #
    vj
    vn
    cF
    @3
    cN
    wph
    cN
    cn
    wcel
    #
    @6
    @13
    poimir.0
    ad2antrr
    @6
    cF
    vy
    cc0
    @11
    cfz
    co
    #
    vj
    vy
    cv
    #
    @3
    clt
    wbr
    #
    @33
    @33
    c1
    caddc
    co
    #
    cif
    #
    @29
    @30
    c1
    vj
    cv
    #
    cfz
    co
    #
    cima
    #
    c1
    csn
    #
    cxp
    #
    @30
    @37
    c1
    caddc
    co
    cN
    cfz
    co
    #
    cima
    #
    cc0
    csn
    #
    cxp
    #
    cun
    #
    caddc
    cof
    #
    co
    #
    csb
    #
    cmpt
    #
    wceq
    #
    wph
    @13
    @6
    @0
    cc0
    cK
    cfzo
    co
    #
    @24
    cmap
    co
    #
    @24
    @24
    vf
    cv
    #
    wf1o
    #
    vf
    cab
    #
    cxp
    #
    cc0
    cN
    cfz
    co
    #
    cxp
    #
    wcel
    #
    @51
    cF
    vy
    @32
    vj
    @33
    vt
    cv
    #
    c2nd
    cfv
    #
    clt
    wbr
    #
    @33
    @35
    cif
    #
    @61
    c1st
    cfv
    #
    c1st
    cfv
    #
    @65
    c2nd
    cfv
    #
    @38
    cima
    #
    @40
    cxp
    #
    @67
    @42
    cima
    #
    @44
    cxp
    #
    cun
    #
    @47
    co
    #
    csb
    #
    cmpt
    #
    wceq
    #
    @51
    vt
    @0
    @59
    cS
    vt
    vz
    weq
    #
    @75
    @50
    cF
    @77
    vy
    @32
    @74
    @49
    @77
    @74
    vj
    @36
    @73
    csb
    @49
    @77
    vj
    @64
    @36
    @73
    @77
    @63
    @34
    @33
    @35
    @77
    @62
    @3
    @33
    clt
    @61
    @0
    c2nd
    fveq2
    breq2d
    ifbid
    csbeq1d
    @77
    vj
    @36
    @73
    @48
    @77
    @66
    @29
    @72
    @46
    @47
    @77
    @65
    @28
    c1st
    @61
    @0
    c1st
    fveq2
    #
    fveq2d
    @77
    @69
    @41
    @71
    @45
    @77
    @68
    @39
    @40
    @77
    @67
    @30
    @38
    @77
    @65
    @28
    c2nd
    @78
    fveq2d
    #
    imaeq1d
    xpeq1d
    @77
    @70
    @43
    @44
    @77
    @67
    @30
    @42
    @79
    imaeq1d
    xpeq1d
    uneq12d
    oveq12d
    csbeq2dv
    eqtrd
    mpteq2dv
    eqeq2d
    poimirlem22.s
    elrab2
    simprbi
    ad2antlr
    @6
    @24
    cz
    @29
    wf
    #
    wph
    @13
    @6
    @24
    @52
    @29
    wf
    #
    @52
    cz
    wss
    #
    @80
    @6
    @29
    @53
    wcel
    #
    @81
    @6
    @28
    @57
    wcel
    #
    @83
    @6
    @60
    @84
    @60
    @0
    @76
    vt
    @59
    crab
    #
    cS
    @76
    vt
    @0
    @59
    elrabi
    poimirlem22.s
    eleq2s
    #
    @0
    @57
    @58
    xp1st
    syl
    #
    @28
    @53
    @56
    xp1st
    syl
    @29
    @52
    @24
    elmapi
    syl
    vn
    @52
    cz
    @23
    cc0
    cK
    elfzoelz
    ssriv
    #
    @24
    @52
    cz
    @29
    fss
    sylancl
    ad2antlr
    @6
    @24
    @24
    @30
    wf1o
    #
    wph
    @13
    @6
    @30
    @56
    wcel
    #
    @89
    @6
    @84
    @90
    @87
    @28
    @53
    @56
    xp2nd
    syl
    @55
    @89
    vf
    @30
    @28
    c2nd
    fvex
    @24
    @24
    @54
    @30
    f1oeq1
    elab
    sylib
    ad2antlr
    @7
    @13
    simpr
    poimirlem1
    wph
    @13
    @26
    @27
    wi
    @6
    wph
    @13
    wa
    #
    @25
    @15
    @3
    @91
    @15
    @3
    wne
    #
    @25
    @91
    @92
    wa
    vy
    cT
    c1st
    cfv
    #
    c1st
    cfv
    #
    @93
    c2nd
    cfv
    #
    vj
    vn
    cF
    @15
    cN
    @3
    wph
    @31
    @13
    @92
    poimir.0
    ad2antrr
    wph
    cF
    vy
    @32
    vj
    @33
    @15
    clt
    wbr
    #
    @33
    @35
    cif
    #
    @94
    @95
    @38
    cima
    #
    @40
    cxp
    #
    @95
    @42
    cima
    #
    @44
    cxp
    #
    cun
    #
    @47
    co
    #
    csb
    #
    cmpt
    #
    wceq
    #
    @13
    @92
    wph
    cT
    cS
    wcel
    #
    @106
    poimirlem22.2
    @107
    cT
    @59
    wcel
    #
    @106
    @76
    @106
    vt
    cT
    @59
    cS
    @61
    cT
    wceq
    #
    @75
    @105
    cF
    @109
    vy
    @32
    @74
    @104
    @109
    @74
    vj
    @97
    @73
    csb
    @104
    @109
    vj
    @64
    @97
    @73
    @109
    @63
    @96
    @33
    @35
    @109
    @62
    @15
    @33
    clt
    @61
    cT
    c2nd
    fveq2
    breq2d
    ifbid
    csbeq1d
    @109
    vj
    @97
    @73
    @103
    @109
    @66
    @94
    @72
    @102
    @47
    @109
    @65
    @93
    c1st
    @61
    cT
    c1st
    fveq2
    #
    fveq2d
    @109
    @69
    @99
    @71
    @101
    @109
    @68
    @98
    @40
    @109
    @67
    @95
    @38
    @109
    @65
    @93
    c2nd
    @110
    fveq2d
    #
    imaeq1d
    xpeq1d
    @109
    @70
    @100
    @44
    @109
    @67
    @95
    @42
    @111
    imaeq1d
    xpeq1d
    uneq12d
    oveq12d
    csbeq2dv
    eqtrd
    mpteq2dv
    eqeq2d
    poimirlem22.s
    elrab2
    simprbi
    syl
    ad2antrr
    wph
    @24
    cz
    @94
    wf
    #
    @13
    @92
    wph
    @24
    @52
    @94
    wf
    #
    @82
    @112
    wph
    @94
    @53
    wcel
    #
    @113
    wph
    @93
    @57
    wcel
    #
    @114
    wph
    @108
    @115
    wph
    @107
    @108
    poimirlem22.2
    @108
    cT
    @85
    cS
    @76
    vt
    cT
    @59
    elrabi
    poimirlem22.s
    eleq2s
    syl
    #
    cT
    @57
    @58
    xp1st
    syl
    #
    @93
    @53
    @56
    xp1st
    syl
    @94
    @52
    @24
    elmapi
    syl
    @88
    @24
    @52
    cz
    @94
    fss
    sylancl
    ad2antrr
    wph
    @24
    @24
    @95
    wf1o
    #
    @13
    @92
    wph
    @95
    @56
    wcel
    #
    @118
    wph
    @115
    @119
    @117
    @93
    @53
    @56
    xp2nd
    syl
    @55
    @118
    vf
    @95
    @93
    c2nd
    fvex
    @24
    @24
    @54
    @95
    f1oeq1
    elab
    sylib
    ad2antrr
    wph
    @13
    @92
    simplr
    @91
    @15
    @58
    wcel
    #
    @92
    @15
    @58
    @3
    csn
    cdif
    wcel
    #
    wph
    @120
    @13
    wph
    @108
    @120
    @116
    cT
    @57
    @58
    xp2nd
    syl
    adantr
    @121
    @120
    @92
    wa
    @15
    @58
    @3
    eldifsn
    biimpri
    sylan
    poimirlem2
    ex
    necon1bd
    adantlr
    mpd
    neeq1d
    exbiri
    mpdi
    necon2bd
    mpd
    @6
    wph
    @3
    @58
    wcel
    #
    @14
    @8
    wa
    #
    @9
    wi
    @6
    @60
    @122
    @86
    @0
    @57
    @58
    xp2nd
    syl
    wph
    @122
    @123
    @9
    wph
    @122
    @123
    wa
    #
    @9
    wph
    @122
    @3
    @24
    wcel
    #
    wn
    #
    wa
    #
    @124
    @9
    wph
    @126
    @123
    @122
    wph
    @126
    @3
    @12
    cN
    csn
    #
    cun
    #
    wcel
    #
    wn
    @123
    wph
    @125
    @130
    wph
    @24
    @129
    @3
    wph
    @24
    @12
    @11
    c1
    caddc
    co
    #
    cN
    cfz
    co
    #
    cun
    #
    @129
    wph
    @131
    c1
    cuz
    cfv
    #
    wcel
    cN
    @11
    cuz
    cfv
    #
    wcel
    @24
    @133
    wceq
    wph
    @131
    cN
    @134
    wph
    cN
    cc
    wcel
    @131
    cN
    wceq
    wph
    cN
    poimir.0
    nncnd
    cN
    npcan1
    syl
    #
    wph
    cN
    cn
    @134
    poimir.0
    nnuz
    syl6eleq
    eqeltrd
    wph
    @131
    cN
    @135
    @136
    wph
    @11
    cz
    wcel
    #
    @11
    @135
    wcel
    @131
    @135
    wcel
    wph
    cN
    cz
    wcel
    #
    @137
    wph
    cN
    poimir.0
    nnzd
    #
    cN
    peano2zm
    syl
    @11
    uzid
    @11
    @11
    peano2uz
    3syl
    eqeltrrd
    @11
    c1
    cN
    fzsplit2
    syl2anc
    wph
    @132
    @128
    @12
    wph
    @132
    cN
    cN
    cfz
    co
    #
    @128
    wph
    @131
    cN
    cN
    cfz
    @136
    oveq1d
    wph
    @138
    @140
    @128
    wceq
    @139
    cN
    fzsn
    syl
    eqtrd
    uneq2d
    eqtrd
    eleq2d
    notbid
    @13
    @4
    wo
    #
    @123
    @130
    @13
    @4
    ioran
    @130
    @13
    @3
    @128
    wcel
    #
    wo
    @141
    @3
    @12
    @128
    elun
    @142
    @4
    @13
    @3
    cN
    @0
    c2nd
    fvex
    #
    elsn
    orbi2i
    bitri
    xchnxbir
    syl6bb
    anbi2d
    wph
    @3
    @58
    @24
    cdif
    #
    wcel
    @3
    @44
    wcel
    @127
    @9
    wph
    @144
    @44
    @3
    wph
    @144
    @44
    cc0
    c1
    caddc
    co
    #
    cN
    cfz
    co
    #
    cun
    #
    @24
    cdif
    #
    @44
    wph
    @58
    @147
    @24
    wph
    cN
    cc0
    cuz
    cfv
    #
    wcel
    @58
    @147
    wceq
    wph
    cN
    cn0
    @149
    wph
    cN
    poimir.0
    nnnn0d
    nn0uz
    syl6eleq
    cc0
    cN
    fzpred
    syl
    difeq1d
    @44
    @24
    cun
    #
    @24
    cdif
    @44
    @24
    cdif
    #
    @148
    @44
    @44
    @24
    difun2
    @147
    @150
    @24
    @146
    @24
    @44
    @145
    c1
    cN
    cfz
    0p1e1
    oveq1i
    uneq2i
    difeq1i
    @44
    @24
    cin
    #
    c0
    wceq
    @44
    @151
    wceq
    @152
    @24
    @44
    cin
    #
    c0
    @44
    @24
    incom
    @153
    c0
    wceq
    cc0
    @24
    wcel
    #
    wn
    @154
    @21
    0nnn
    cc0
    cN
    elfznn
    mto
    @24
    cc0
    disjsn
    mpbir
    eqtri
    @44
    @24
    disj3
    mpbi
    3eqtr4i
    syl6eq
    eleq2d
    @3
    @58
    @24
    eldif
    @3
    cc0
    @143
    elsn
    3bitr3g
    bitr3d
    biimpd
    expdimp
    sylan2
    mpand
    @7
    @9
    @16
    @10
    @17
    @7
    @9
    vs
    cv
    #
    c2nd
    cfv
    #
    cc0
    wceq
    #
    wa
    #
    vz
    vs
    weq
    #
    wi
    #
    vs
    cS
    wral
    #
    @107
    @9
    @16
    wa
    #
    @10
    wi
    #
    wph
    @161
    vz
    cS
    wph
    @9
    vz
    cS
    wrmo
    @161
    vz
    cS
    wral
    wph
    vy
    vz
    vt
    cS
    vf
    vj
    cF
    cK
    cN
    poimir.0
    poimirlem22.s
    poimirlem22.1
    poimirlem13
    @9
    @157
    vz
    vs
    cS
    @159
    @3
    @156
    cc0
    @0
    @155
    c2nd
    fveq2
    eqeq1d
    rmo4
    sylib
    r19.21bi
    wph
    @107
    @6
    poimirlem22.2
    adantr
    @160
    @163
    vs
    cT
    cS
    @155
    cT
    wceq
    #
    @158
    @162
    @159
    @10
    @164
    @157
    @16
    @9
    @164
    @156
    @15
    cc0
    @155
    cT
    c2nd
    fveq2
    eqeq1d
    anbi2d
    @155
    cT
    @0
    eqeq2
    imbi12d
    rspccv
    sylc
    mpan2d
    syld
    necon1ad
    ralrimiva
    wph
    vy
    vz
    vt
    cS
    vf
    vj
    cF
    cK
    cN
    poimir.0
    poimirlem22.s
    poimirlem22.1
    poimirlem14
    @1
    @4
    vz
    cS
    rmoim
    sylc
    @1
    vz
    cS
    reu5
    sylanbrc
end
