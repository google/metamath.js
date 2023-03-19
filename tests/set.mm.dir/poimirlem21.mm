include "cv.mm"
include "wne.mm"
include "wrex.mm"
include "wrmo.mm"
include "wreu.mm"
include "poimirlem20.mm"
include "c2nd.mm"
include "cfv.mm"
include "cc0.mm"
include "wceq.mm"
include "wi.mm"
include "wral.mm"
include "wcel.mm"
include "wa.mm"
include "wn.mm"
include "c1.mm"
include "cmin.mm"
include "co.mm"
include "cfz.mm"
include "adantr.mm"
include "cle.mm"
include "wbr.mm"
include "clt.mm"
include "nnred.mm"
include "ltm1d.mm"
include "cn.mm"
include "cn0.mm"
include "nnm1nn0.mm"
include "syl.mm"
include "nn0red.mm"
include "ltnled.mm"
include "mpbid.mm"
include "elfzle2.mm"
include "nsyl.mm"
include "eleq1.mm"
include "notbid.mm"
include "syl5ibrcom.mm"
include "necon2ad.mm"
include "c1st.mm"
include "ad2antrr.mm"
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
include "mpdd.mm"
include "necon2bd.mm"
include "cuz.mm"
include "nn0uz.mm"
include "syl6eleq.mm"
include "fzpred.mm"
include "0p1e1.mm"
include "oveq1i.mm"
include "uneq2i.mm"
include "syl6eq.mm"
include "eleq2d.mm"
include "wo.mm"
include "ioran.mm"
include "elun.mm"
include "elsn.mm"
include "orbi1i.mm"
include "bitri.mm"
include "xchnxbir.mm"
include "syl6bb.mm"
include "anbi2d.mm"
include "uncom.mm"
include "difeq1i.mm"
include "difun2.mm"
include "eqtri.mm"
include "cc.mm"
include "nncnd.mm"
include "npcan1.mm"
include "nnnn0d.mm"
include "eqeltrd.mm"
include "nn0zd.mm"
include "uzid.mm"
include "peano2uz.mm"
include "3syl.mm"
include "eqeltrrd.mm"
include "fzsplit2.mm"
include "syl2anc.mm"
include "oveq1d.mm"
include "nnzd.mm"
include "fzsn.mm"
include "uneq2d.mm"
include "difeq1d.mm"
include "cin.mm"
include "c0.mm"
include "incom.mm"
include "eqeq1i.mm"
include "disjsn.mm"
include "disj3.mm"
include "3bitr3i.mm"
include "3eqtr4a.mm"
include "eldif.mm"
include "3bitr3g.mm"
include "bitr3d.mm"
include "biimpd.mm"
include "expdimp.mm"
include "sylan2.mm"
include "mpan2d.mm"
include "poimirlem14.mm"
include "eqeq1d.mm"
include "rmo4.mm"
include "r19.21bi.mm"
include "eqeq2.mm"
include "imbi12d.mm"
include "rspccv.mm"
include "sylc.mm"
include "syld.mm"
include "necon1ad.mm"
include "ralrimiva.mm"
include "poimirlem13.mm"
include "rmoim.mm"
include "reu5.mm"
include "sylanbrc.mm"

theorem poimirlem21
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
  assume poimirlem22.3: |- ( ( ph /\ n e. ( 1 ... N ) ) -> E. p e. ran F ( p ` n ) =/= 0 )
  assume poimirlem21.4: |- ( ph -> ( 2nd ` T ) = N )

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
    poimirlem22.3
    poimirlem21.4
    poimirlem20
    wph
    @1
    @0
    c2nd
    cfv
    #
    cc0
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
    cN
    wceq
    #
    @0
    cT
    wceq
    #
    @7
    @8
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
    @9
    @7
    cT
    c2nd
    cfv
    #
    cN
    wceq
    #
    @14
    wph
    @16
    @6
    poimirlem21.4
    adantr
    #
    @7
    @13
    @15
    cN
    @7
    @13
    @3
    cN
    wne
    #
    @15
    cN
    wne
    #
    wph
    @13
    @18
    wi
    @6
    wph
    @13
    @3
    cN
    wph
    @14
    @9
    cN
    @12
    wcel
    #
    wn
    wph
    cN
    @11
    cle
    wbr
    #
    @20
    wph
    @11
    cN
    clt
    wbr
    @21
    wn
    wph
    cN
    wph
    cN
    poimir.0
    nnred
    #
    ltm1d
    wph
    @11
    cN
    wph
    @11
    wph
    cN
    cn
    wcel
    #
    @11
    cn0
    wcel
    poimir.0
    cN
    nnm1nn0
    syl
    #
    nn0red
    @22
    ltnled
    mpbid
    #
    cN
    c1
    @11
    elfzle2
    nsyl
    @9
    @13
    @20
    @3
    cN
    @12
    eleq1
    notbid
    syl5ibrcom
    necon2ad
    adantr
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
    cN
    @26
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
    @27
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
    @26
    vy
    @0
    c1st
    cfv
    #
    c1st
    cfv
    #
    @32
    c2nd
    cfv
    #
    vj
    vn
    cF
    @3
    cN
    wph
    @23
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
    @36
    @36
    c1
    caddc
    co
    #
    cif
    #
    @33
    @34
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
    @34
    @40
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
    @28
    cmap
    co
    #
    @28
    @28
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
    @54
    cF
    vy
    @35
    vj
    @36
    vt
    cv
    #
    c2nd
    cfv
    #
    clt
    wbr
    #
    @36
    @38
    cif
    #
    @64
    c1st
    cfv
    #
    c1st
    cfv
    #
    @68
    c2nd
    cfv
    #
    @41
    cima
    #
    @43
    cxp
    #
    @70
    @45
    cima
    #
    @47
    cxp
    #
    cun
    #
    @50
    co
    #
    csb
    #
    cmpt
    #
    wceq
    #
    @54
    vt
    @0
    @62
    cS
    vt
    vz
    weq
    #
    @78
    @53
    cF
    @80
    vy
    @35
    @77
    @52
    @80
    @77
    vj
    @39
    @76
    csb
    @52
    @80
    vj
    @67
    @39
    @76
    @80
    @66
    @37
    @36
    @38
    @80
    @65
    @3
    @36
    clt
    @64
    @0
    c2nd
    fveq2
    breq2d
    ifbid
    csbeq1d
    @80
    vj
    @39
    @76
    @51
    @80
    @69
    @33
    @75
    @49
    @50
    @80
    @68
    @32
    c1st
    @64
    @0
    c1st
    fveq2
    #
    fveq2d
    @80
    @72
    @44
    @74
    @48
    @80
    @71
    @42
    @43
    @80
    @70
    @34
    @41
    @80
    @68
    @32
    c2nd
    @81
    fveq2d
    #
    imaeq1d
    xpeq1d
    @80
    @73
    @46
    @47
    @80
    @70
    @34
    @45
    @82
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
    @28
    cz
    @33
    wf
    #
    wph
    @13
    @6
    @28
    @55
    @33
    wf
    #
    @55
    cz
    wss
    #
    @83
    @6
    @33
    @56
    wcel
    #
    @84
    @6
    @32
    @60
    wcel
    #
    @86
    @6
    @63
    @87
    @63
    @0
    @79
    vt
    @62
    crab
    #
    cS
    @79
    vt
    @0
    @62
    elrabi
    poimirlem22.s
    eleq2s
    #
    @0
    @60
    @61
    xp1st
    syl
    #
    @32
    @56
    @59
    xp1st
    syl
    @33
    @55
    @28
    elmapi
    syl
    vn
    @55
    cz
    @27
    cc0
    cK
    elfzoelz
    ssriv
    #
    @28
    @55
    cz
    @33
    fss
    sylancl
    ad2antlr
    @6
    @28
    @28
    @34
    wf1o
    #
    wph
    @13
    @6
    @34
    @59
    wcel
    #
    @92
    @6
    @87
    @93
    @90
    @32
    @56
    @59
    xp2nd
    syl
    @58
    @92
    vf
    @34
    @32
    c2nd
    fvex
    @28
    @28
    @57
    @34
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
    @30
    @31
    wi
    @6
    wph
    @13
    wa
    #
    @29
    @15
    @3
    @94
    @15
    @3
    wne
    #
    @29
    @94
    @95
    wa
    vy
    cT
    c1st
    cfv
    #
    c1st
    cfv
    #
    @96
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
    @23
    @13
    @95
    poimir.0
    ad2antrr
    wph
    cF
    vy
    @35
    vj
    @36
    @15
    clt
    wbr
    #
    @36
    @38
    cif
    #
    @97
    @98
    @41
    cima
    #
    @43
    cxp
    #
    @98
    @45
    cima
    #
    @47
    cxp
    #
    cun
    #
    @50
    co
    #
    csb
    #
    cmpt
    #
    wceq
    #
    @13
    @95
    wph
    cT
    cS
    wcel
    #
    @109
    poimirlem22.2
    @110
    cT
    @62
    wcel
    #
    @109
    @79
    @109
    vt
    cT
    @62
    cS
    @64
    cT
    wceq
    #
    @78
    @108
    cF
    @112
    vy
    @35
    @77
    @107
    @112
    @77
    vj
    @100
    @76
    csb
    @107
    @112
    vj
    @67
    @100
    @76
    @112
    @66
    @99
    @36
    @38
    @112
    @65
    @15
    @36
    clt
    @64
    cT
    c2nd
    fveq2
    breq2d
    ifbid
    csbeq1d
    @112
    vj
    @100
    @76
    @106
    @112
    @69
    @97
    @75
    @105
    @50
    @112
    @68
    @96
    c1st
    @64
    cT
    c1st
    fveq2
    #
    fveq2d
    @112
    @72
    @102
    @74
    @104
    @112
    @71
    @101
    @43
    @112
    @70
    @98
    @41
    @112
    @68
    @96
    c2nd
    @113
    fveq2d
    #
    imaeq1d
    xpeq1d
    @112
    @73
    @103
    @47
    @112
    @70
    @98
    @45
    @114
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
    @28
    cz
    @97
    wf
    #
    @13
    @95
    wph
    @28
    @55
    @97
    wf
    #
    @85
    @115
    wph
    @97
    @56
    wcel
    #
    @116
    wph
    @96
    @60
    wcel
    #
    @117
    wph
    @111
    @118
    wph
    @110
    @111
    poimirlem22.2
    @111
    cT
    @88
    cS
    @79
    vt
    cT
    @62
    elrabi
    poimirlem22.s
    eleq2s
    syl
    #
    cT
    @60
    @61
    xp1st
    syl
    #
    @96
    @56
    @59
    xp1st
    syl
    @97
    @55
    @28
    elmapi
    syl
    @91
    @28
    @55
    cz
    @97
    fss
    sylancl
    ad2antrr
    wph
    @28
    @28
    @98
    wf1o
    #
    @13
    @95
    wph
    @98
    @59
    wcel
    #
    @121
    wph
    @118
    @122
    @120
    @96
    @56
    @59
    xp2nd
    syl
    @58
    @121
    vf
    @98
    @96
    c2nd
    fvex
    @28
    @28
    @57
    @98
    f1oeq1
    elab
    sylib
    ad2antrr
    wph
    @13
    @95
    simplr
    @94
    @15
    @61
    wcel
    #
    @95
    @15
    @61
    @3
    csn
    cdif
    wcel
    #
    wph
    @123
    @13
    wph
    @111
    @123
    @119
    cT
    @60
    @61
    xp2nd
    syl
    adantr
    @124
    @123
    @95
    wa
    @15
    @61
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
    mpdd
    necon2bd
    mpd
    @6
    wph
    @3
    @61
    wcel
    #
    @8
    @14
    wa
    #
    @9
    wi
    @6
    @63
    @125
    @89
    @0
    @60
    @61
    xp2nd
    syl
    wph
    @125
    @126
    @9
    wph
    @125
    @126
    wa
    #
    @9
    wph
    @125
    @3
    @35
    wcel
    #
    wn
    #
    wa
    #
    @127
    @9
    wph
    @129
    @126
    @125
    wph
    @129
    @3
    @47
    @12
    cun
    #
    wcel
    #
    wn
    @126
    wph
    @128
    @132
    wph
    @35
    @131
    @3
    wph
    @35
    @47
    cc0
    c1
    caddc
    co
    #
    @11
    cfz
    co
    #
    cun
    #
    @131
    wph
    @11
    cc0
    cuz
    cfv
    #
    wcel
    @35
    @135
    wceq
    wph
    @11
    cn0
    @136
    @24
    nn0uz
    syl6eleq
    cc0
    @11
    fzpred
    syl
    @134
    @12
    @47
    @133
    c1
    @11
    cfz
    0p1e1
    oveq1i
    uneq2i
    syl6eq
    eleq2d
    notbid
    @4
    @13
    wo
    #
    @126
    @132
    @4
    @13
    ioran
    @132
    @3
    @47
    wcel
    #
    @13
    wo
    @137
    @3
    @47
    @12
    elun
    @138
    @4
    @13
    @3
    cc0
    @0
    c2nd
    fvex
    #
    elsn
    orbi1i
    bitri
    xchnxbir
    syl6bb
    anbi2d
    wph
    @3
    @61
    @35
    cdif
    #
    wcel
    @3
    cN
    csn
    #
    wcel
    @130
    @9
    wph
    @140
    @141
    @3
    wph
    @35
    @141
    cun
    #
    @35
    cdif
    #
    @141
    @35
    cdif
    #
    @140
    @141
    @143
    @141
    @35
    cun
    #
    @35
    cdif
    @144
    @142
    @145
    @35
    @35
    @141
    uncom
    difeq1i
    @141
    @35
    difun2
    eqtri
    wph
    @61
    @142
    @35
    wph
    @61
    @35
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
    @142
    wph
    @146
    @136
    wcel
    cN
    @11
    cuz
    cfv
    #
    wcel
    @61
    @148
    wceq
    wph
    @146
    cN
    @136
    wph
    cN
    cc
    wcel
    @146
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
    cn0
    @136
    wph
    cN
    poimir.0
    nnnn0d
    nn0uz
    syl6eleq
    eqeltrd
    wph
    @146
    cN
    @149
    @150
    wph
    @11
    cz
    wcel
    @11
    @149
    wcel
    @146
    @149
    wcel
    wph
    @11
    @24
    nn0zd
    @11
    uzid
    @11
    @11
    peano2uz
    3syl
    eqeltrrd
    @11
    cc0
    cN
    fzsplit2
    syl2anc
    wph
    @147
    @141
    @35
    wph
    @147
    cN
    cN
    cfz
    co
    #
    @141
    wph
    @146
    cN
    cN
    cfz
    @150
    oveq1d
    wph
    cN
    cz
    wcel
    @151
    @141
    wceq
    wph
    cN
    poimir.0
    nnzd
    cN
    fzsn
    syl
    eqtrd
    uneq2d
    eqtrd
    difeq1d
    wph
    cN
    @35
    wcel
    #
    wn
    #
    @141
    @144
    wceq
    #
    wph
    @21
    @152
    @25
    cN
    cc0
    @11
    elfzle2
    nsyl
    @35
    @141
    cin
    #
    c0
    wceq
    @141
    @35
    cin
    #
    c0
    wceq
    @153
    @154
    @155
    @156
    c0
    @35
    @141
    incom
    eqeq1i
    @35
    cN
    disjsn
    @141
    @35
    disj3
    3bitr3i
    sylib
    3eqtr4a
    eleq2d
    @3
    @61
    @35
    eldif
    @3
    cN
    @139
    elsn
    3bitr3g
    bitr3d
    biimpd
    expdimp
    sylan2
    mpan2d
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
    cN
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
    @110
    @9
    @16
    wa
    #
    @10
    wi
    #
    wph
    @163
    vz
    cS
    wph
    @9
    vz
    cS
    wrmo
    @163
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
    poimirlem14
    @9
    @159
    vz
    vs
    cS
    @161
    @3
    @158
    cN
    @0
    @157
    c2nd
    fveq2
    eqeq1d
    rmo4
    sylib
    r19.21bi
    wph
    @110
    @6
    poimirlem22.2
    adantr
    @162
    @165
    vs
    cT
    cS
    @157
    cT
    wceq
    #
    @160
    @164
    @161
    @10
    @166
    @159
    @16
    @9
    @166
    @158
    @15
    cN
    @157
    cT
    c2nd
    fveq2
    eqeq1d
    anbi2d
    @157
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
    poimirlem13
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
