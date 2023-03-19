include "c1st.mm"
include "cfv.mm"
include "c2nd.mm"
include "c1.mm"
include "cfz.mm"
include "co.mm"
include "cima.mm"
include "cv.mm"
include "wcel.mm"
include "wn.mm"
include "wa.mm"
include "wi.mm"
include "caddc.mm"
include "wceq.mm"
include "cmin.mm"
include "cdif.mm"
include "eldif.mm"
include "crn.mm"
include "imassrn.mm"
include "wf.mm"
include "wss.mm"
include "wf1o.mm"
include "cab.mm"
include "cc0.mm"
include "cfzo.mm"
include "cmap.mm"
include "cxp.mm"
include "clt.mm"
include "wbr.mm"
include "cif.mm"
include "csn.mm"
include "cun.mm"
include "cof.mm"
include "csb.mm"
include "cmpt.mm"
include "crab.mm"
include "elrabi.mm"
include "eleq2s.mm"
include "syl.mm"
include "xp1st.mm"
include "xp2nd.mm"
include "fvex.mm"
include "f1oeq1.mm"
include "elab.mm"
include "sylib.mm"
include "f1of.mm"
include "frn.mm"
include "syl5ss.mm"
include "wfo.mm"
include "f1ofo.mm"
include "foima.mm"
include "sseqtr4d.mm"
include "ssdifd.mm"
include "ccnv.mm"
include "wfun.mm"
include "dff1o3.mm"
include "simprbi.mm"
include "imadif.mm"
include "difun2.mm"
include "fzsplit.mm"
include "uncom.mm"
include "syl6eq.mm"
include "difeq1d.mm"
include "cin.mm"
include "c0.mm"
include "incom.mm"
include "cn.mm"
include "elfznn.mm"
include "nnred.mm"
include "ltp1d.mm"
include "fzdisj.mm"
include "syl5eq.mm"
include "disj3.mm"
include "3eqtr4a.mm"
include "imaeq2d.mm"
include "eqtr3d.mm"
include "sseqtrd.mm"
include "sselda.mm"
include "sylan2br.mm"
include "cvv.mm"
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
include "wb.mm"
include "breq12.mm"
include "sylan2.mm"
include "ancoms.mm"
include "oveq1.mm"
include "cc.mm"
include "nncnd.mm"
include "npcan1.mm"
include "sylan9eqr.mm"
include "ifbieq2d.mm"
include "cle.mm"
include "cz.mm"
include "nnzd.mm"
include "elfzm1b.mm"
include "syl2anc.mm"
include "mpbid.mm"
include "elfzle1.mm"
include "0red.mm"
include "cn0.mm"
include "nnm1nn0.mm"
include "nn0red.mm"
include "lenltd.mm"
include "iffalsed.mm"
include "adantr.mm"
include "oveq2.mm"
include "oveq1d.mm"
include "oveq2d.mm"
include "adantl.mm"
include "csbied.mm"
include "ovexd.mm"
include "fvmptd.mm"
include "fveq1d.mm"
include "wfn.mm"
include "elmapfn.mm"
include "1ex.mm"
include "fnconstg.mm"
include "ax-mp.mm"
include "c0ex.mm"
include "pm3.2i.mm"
include "imain.mm"
include "ima0.mm"
include "fnun.mm"
include "sylancr.mm"
include "imaundi.mm"
include "syl5eqr.mm"
include "fneq2d.mm"
include "inidm.mm"
include "eqidd.mm"
include "fvun2.mm"
include "mp3an12.mm"
include "sylan.mm"
include "fvconst2.mm"
include "ofval.mm"
include "mpdan.mm"
include "elmapi.mm"
include "ffvelrnda.mm"
include "elfzonn0.mm"
include "nn0cnd.mm"
include "syldan.mm"
include "addid1d.mm"
include "3eqtrd.mm"
include "fvun1.mm"
include "adantrr.mm"
include "poimirlem10.mm"
include "3eqtr3d.mm"
include "wne.mm"
include "gtned.mm"
include "neneqd.mm"
include "pm2.65da.mm"
include "iman.mm"
include "sylibr.mm"
include "ssrdv.mm"

theorem poimirlem11
  let wph: wff ph
  let vy: setvar y
  let vt: setvar t
  let cS: class S
  let cT: class T
  let cU: class U
  let vf: setvar f
  let vj: setvar j
  let cF: class F
  let cK: class K
  let cM: class M
  let cN: class N
  let vk: setvar k
  let vm: setvar m
  let vn: setvar n
  let vp: setvar p
  let vs: setvar s
  let vz: setvar z
  let vi: setvar i
  let vq: setvar q
  let vu: setvar u
  let vw: setvar w
  let vx: setvar x
  let cV: class V
  let cB: class B
  assume poimir.0: |- ( ph -> N e. NN )
  assume poimirlem22.s: |- S = { t e. ( ( ( ( 0 ..^ K ) ^m ( 1 ... N ) ) X. { f | f : ( 1 ... N ) -1-1-onto-> ( 1 ... N ) } ) X. ( 0 ... N ) ) | F = ( y e. ( 0 ... ( N - 1 ) ) |-> [_ if ( y < ( 2nd ` t ) , y , ( y + 1 ) ) / j ]_ ( ( 1st ` ( 1st ` t ) ) oF + ( ( ( ( 2nd ` ( 1st ` t ) ) " ( 1 ... j ) ) X. { 1 } ) u. ( ( ( 2nd ` ( 1st ` t ) ) " ( ( j + 1 ) ... N ) ) X. { 0 } ) ) ) ) }
  assume poimirlem22.1: |- ( ph -> F : ( 0 ... ( N - 1 ) ) --> ( ( 0 ... K ) ^m ( 1 ... N ) ) )
  assume poimirlem12.2: |- ( ph -> T e. S )
  assume poimirlem11.3: |- ( ph -> ( 2nd ` T ) = 0 )
  assume poimirlem11.4: |- ( ph -> U e. S )
  assume poimirlem11.5: |- ( ph -> ( 2nd ` U ) = 0 )
  assume poimirlem11.6: |- ( ph -> M e. ( 1 ... N ) )

  disjoint j t
  disjoint j y
  disjoint S j
  disjoint t y
  disjoint S t
  disjoint S y
  disjoint f j
  disjoint f t
  disjoint f y
  disjoint j t
  disjoint j y
  disjoint t y
  disjoint j ph
  disjoint ph y
  disjoint F j
  disjoint F y
  disjoint M j
  disjoint M y
  disjoint N j
  disjoint N y
  disjoint T j
  disjoint T y
  disjoint U j
  disjoint U y
  disjoint ph t
  disjoint K f
  disjoint K j
  disjoint K t
  disjoint M f
  disjoint M t
  disjoint N f
  disjoint N t
  disjoint T f
  disjoint U f
  disjoint F f
  disjoint F t
  disjoint T t
  disjoint U t
  disjoint j k
  disjoint j m
  disjoint j n
  disjoint j p
  disjoint j s
  disjoint j z
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
  disjoint n p
  disjoint n s
  disjoint n t
  disjoint n y
  disjoint n z
  disjoint S n
  disjoint p s
  disjoint p t
  disjoint p y
  disjoint p z
  disjoint S p
  disjoint s t
  disjoint s y
  disjoint s z
  disjoint S s
  disjoint t z
  disjoint y z
  disjoint S z
  disjoint f i
  disjoint f k
  disjoint f m
  disjoint f n
  disjoint f p
  disjoint f q
  disjoint f s
  disjoint f u
  disjoint f w
  disjoint f x
  disjoint f z
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
  disjoint j n
  disjoint j p
  disjoint j q
  disjoint j s
  disjoint j u
  disjoint j w
  disjoint j x
  disjoint j z
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
  disjoint n p
  disjoint n q
  disjoint n s
  disjoint n t
  disjoint n u
  disjoint n w
  disjoint n x
  disjoint n y
  disjoint n z
  disjoint p q
  disjoint p s
  disjoint p t
  disjoint p u
  disjoint p w
  disjoint p x
  disjoint p y
  disjoint p z
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
  disjoint t z
  disjoint u w
  disjoint u x
  disjoint u y
  disjoint u z
  disjoint w x
  disjoint w y
  disjoint w z
  disjoint x y
  disjoint x z
  disjoint y z
  disjoint m ph
  disjoint n ph
  disjoint F m
  disjoint F n
  disjoint M m
  disjoint M n
  disjoint N m
  disjoint N n
  disjoint T m
  disjoint T n
  disjoint U m
  disjoint U n
  disjoint V j
  disjoint V m
  disjoint V n
  disjoint V y
  disjoint i ph
  disjoint k ph
  disjoint p ph
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
  disjoint K n
  disjoint K p
  disjoint K s
  disjoint M i
  disjoint M k
  disjoint M p
  disjoint M s
  disjoint N i
  disjoint N k
  disjoint N p
  disjoint N s
  disjoint T i
  disjoint T p
  disjoint U i
  disjoint U p
  disjoint ph z
  disjoint F k
  disjoint F p
  disjoint F s
  disjoint F z
  disjoint K z
  disjoint N z
  disjoint T k
  disjoint T s
  disjoint T z
  disjoint U k
  assert |- ( ph -> ( ( 2nd ` ( 1st ` T ) ) " ( 1 ... M ) ) C_ ( ( 2nd ` ( 1st ` U ) ) " ( 1 ... M ) ) )

  proof
    wph
    vy
    cT
    c1st
    cfv
    #
    c2nd
    cfv
    #
    c1
    cM
    cfz
    co
    #
    cima
    #
    cU
    c1st
    cfv
    #
    c2nd
    cfv
    #
    @2
    cima
    #
    wph
    vy
    cv
    #
    @3
    wcel
    #
    @7
    @6
    wcel
    #
    wn
    #
    wa
    #
    wn
    @8
    @9
    wi
    wph
    @11
    @7
    @0
    c1st
    cfv
    #
    cfv
    #
    c1
    caddc
    co
    #
    @13
    wceq
    #
    wph
    @11
    wa
    @7
    cM
    c1
    cmin
    co
    #
    cF
    cfv
    #
    cfv
    #
    @7
    @4
    c1st
    cfv
    #
    cfv
    #
    @14
    @13
    wph
    @11
    @7
    @5
    cM
    c1
    caddc
    co
    #
    cN
    cfz
    co
    #
    cima
    #
    wcel
    #
    @18
    @20
    wceq
    @11
    wph
    @7
    @3
    @6
    cdif
    #
    wcel
    @24
    @7
    @3
    @6
    eldif
    wph
    @25
    @23
    @7
    wph
    @25
    @5
    c1
    cN
    cfz
    co
    #
    cima
    #
    @6
    cdif
    #
    @23
    wph
    @3
    @27
    @6
    wph
    @3
    @26
    @27
    wph
    @3
    @1
    crn
    #
    @26
    @1
    @2
    imassrn
    wph
    @26
    @26
    @1
    wf
    #
    @29
    @26
    wss
    wph
    @26
    @26
    @1
    wf1o
    #
    @30
    wph
    @1
    @26
    @26
    vf
    cv
    #
    wf1o
    #
    vf
    cab
    #
    wcel
    #
    @31
    wph
    @0
    cc0
    cK
    cfzo
    co
    #
    @26
    cmap
    co
    #
    @34
    cxp
    #
    wcel
    #
    @35
    wph
    cT
    @38
    cc0
    cN
    cfz
    co
    #
    cxp
    #
    wcel
    #
    @39
    wph
    cT
    cS
    wcel
    #
    @42
    poimirlem12.2
    @42
    cT
    cF
    vy
    cc0
    cN
    c1
    cmin
    co
    #
    cfz
    co
    #
    vj
    @7
    vt
    cv
    #
    c2nd
    cfv
    #
    clt
    wbr
    #
    @7
    @7
    c1
    caddc
    co
    #
    cif
    #
    @46
    c1st
    cfv
    #
    c1st
    cfv
    #
    @51
    c2nd
    cfv
    #
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
    @53
    @54
    c1
    caddc
    co
    #
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
    vt
    @41
    crab
    #
    cS
    @69
    vt
    cT
    @41
    elrabi
    poimirlem22.s
    eleq2s
    syl
    cT
    @38
    @40
    xp1st
    syl
    #
    @0
    @37
    @34
    xp2nd
    syl
    @33
    @31
    vf
    @1
    @0
    c2nd
    fvex
    @26
    @26
    @32
    @1
    f1oeq1
    elab
    sylib
    #
    @26
    @26
    @1
    f1of
    syl
    @26
    @26
    @1
    frn
    syl
    syl5ss
    #
    wph
    @26
    @26
    @5
    wfo
    #
    @27
    @26
    wceq
    wph
    @26
    @26
    @5
    wf1o
    #
    @74
    wph
    @5
    @34
    wcel
    #
    @75
    wph
    @4
    @38
    wcel
    #
    @76
    wph
    cU
    @41
    wcel
    #
    @77
    wph
    cU
    cS
    wcel
    #
    @78
    poimirlem11.4
    @78
    cU
    @70
    cS
    @69
    vt
    cU
    @41
    elrabi
    poimirlem22.s
    eleq2s
    syl
    cU
    @38
    @40
    xp1st
    syl
    #
    @4
    @37
    @34
    xp2nd
    syl
    @33
    @75
    vf
    @5
    @4
    c2nd
    fvex
    @26
    @26
    @32
    @5
    f1oeq1
    elab
    sylib
    #
    @26
    @26
    @5
    f1ofo
    syl
    @26
    @26
    @5
    foima
    syl
    #
    sseqtr4d
    ssdifd
    wph
    @5
    @26
    @2
    cdif
    #
    cima
    #
    @28
    @23
    wph
    @5
    ccnv
    wfun
    #
    @84
    @28
    wceq
    wph
    @75
    @85
    @81
    @75
    @74
    @85
    @26
    @26
    @5
    dff1o3
    simprbi
    syl
    #
    @26
    @2
    @5
    imadif
    syl
    wph
    @83
    @22
    @5
    wph
    @22
    @2
    cun
    #
    @2
    cdif
    @22
    @2
    cdif
    #
    @83
    @22
    @22
    @2
    difun2
    wph
    @26
    @87
    @2
    wph
    @26
    @2
    @22
    cun
    #
    @87
    wph
    cM
    @26
    wcel
    #
    @26
    @89
    wceq
    poimirlem11.6
    cM
    c1
    cN
    fzsplit
    syl
    #
    @2
    @22
    uncom
    syl6eq
    difeq1d
    wph
    @22
    @2
    cin
    #
    c0
    wceq
    @22
    @88
    wceq
    wph
    @92
    @2
    @22
    cin
    #
    c0
    @22
    @2
    incom
    wph
    cM
    @21
    clt
    wbr
    @93
    c0
    wceq
    wph
    cM
    wph
    cM
    wph
    @90
    cM
    cn
    wcel
    #
    poimirlem11.6
    cM
    cN
    elfznn
    syl
    #
    nnred
    ltp1d
    c1
    cM
    @21
    cN
    fzdisj
    syl
    #
    syl5eq
    @22
    @2
    disj3
    sylib
    3eqtr4a
    imaeq2d
    eqtr3d
    sseqtrd
    sselda
    sylan2br
    wph
    @24
    wa
    #
    @18
    @7
    @19
    @6
    @57
    cxp
    #
    @23
    @62
    cxp
    #
    cun
    #
    @65
    co
    #
    cfv
    #
    @20
    cc0
    caddc
    co
    #
    @20
    wph
    @18
    @102
    wceq
    @24
    wph
    @7
    @17
    @101
    wph
    vy
    @16
    vj
    @7
    cU
    c2nd
    cfv
    #
    clt
    wbr
    #
    @7
    @49
    cif
    #
    @19
    @5
    @55
    cima
    #
    @57
    cxp
    #
    @5
    @60
    cima
    #
    @62
    cxp
    #
    cun
    #
    @65
    co
    #
    csb
    #
    @101
    @45
    cF
    cvv
    wph
    @79
    cF
    vy
    @45
    @113
    cmpt
    #
    wceq
    #
    poimirlem11.4
    @79
    @78
    @115
    @69
    @115
    vt
    cU
    @41
    cS
    @46
    cU
    wceq
    #
    @68
    @114
    cF
    @116
    vy
    @45
    @67
    @113
    @116
    @67
    vj
    @106
    @66
    csb
    @113
    @116
    vj
    @50
    @106
    @66
    @116
    @48
    @105
    @7
    @49
    @116
    @47
    @104
    @7
    clt
    @46
    cU
    c2nd
    fveq2
    breq2d
    ifbid
    csbeq1d
    @116
    vj
    @106
    @66
    @112
    @116
    @52
    @19
    @64
    @111
    @65
    @116
    @51
    @4
    c1st
    @46
    cU
    c1st
    fveq2
    #
    fveq2d
    @116
    @58
    @108
    @63
    @110
    @116
    @56
    @107
    @57
    @116
    @53
    @5
    @55
    @116
    @51
    @4
    c2nd
    @117
    fveq2d
    #
    imaeq1d
    xpeq1d
    @116
    @61
    @109
    @62
    @116
    @53
    @5
    @60
    @118
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
    wph
    @7
    @16
    wceq
    #
    wa
    #
    @113
    vj
    cM
    @112
    csb
    #
    @101
    @120
    vj
    @106
    cM
    @112
    @120
    @106
    @16
    cc0
    clt
    wbr
    #
    @7
    cM
    cif
    #
    cM
    @120
    @105
    @122
    @49
    cM
    @7
    @119
    wph
    @105
    @122
    wb
    #
    wph
    @119
    @104
    cc0
    wceq
    @124
    poimirlem11.5
    @7
    @16
    @104
    cc0
    clt
    breq12
    sylan2
    ancoms
    @119
    wph
    @49
    @16
    c1
    caddc
    co
    #
    cM
    @7
    @16
    c1
    caddc
    oveq1
    wph
    cM
    cc
    wcel
    @125
    cM
    wceq
    wph
    cM
    @95
    nncnd
    cM
    npcan1
    syl
    sylan9eqr
    #
    ifbieq2d
    wph
    @123
    cM
    wceq
    @119
    wph
    @122
    @7
    cM
    wph
    cc0
    @16
    cle
    wbr
    #
    @122
    wn
    wph
    @16
    @45
    wcel
    #
    @127
    wph
    @90
    @128
    poimirlem11.6
    wph
    cM
    cz
    wcel
    cN
    cz
    wcel
    @90
    @128
    wb
    wph
    cM
    @95
    nnzd
    wph
    cN
    poimir.0
    nnzd
    cM
    cN
    elfzm1b
    syl2anc
    mpbid
    #
    @16
    cc0
    @44
    elfzle1
    syl
    wph
    cc0
    @16
    wph
    0red
    wph
    @16
    wph
    @94
    @16
    cn0
    wcel
    @95
    cM
    nnm1nn0
    syl
    nn0red
    lenltd
    mpbid
    iffalsed
    adantr
    #
    eqtrd
    csbeq1d
    wph
    @121
    @101
    wceq
    @119
    wph
    vj
    cM
    @112
    @101
    @26
    poimirlem11.6
    @54
    cM
    wceq
    #
    @112
    @101
    wceq
    wph
    @131
    @111
    @100
    @19
    @65
    @131
    @108
    @98
    @110
    @99
    @131
    @107
    @6
    @57
    @131
    @55
    @2
    @5
    @54
    cM
    c1
    cfz
    oveq2
    #
    imaeq2d
    xpeq1d
    @131
    @109
    @23
    @62
    @131
    @60
    @22
    @5
    @131
    @59
    @21
    cN
    cfz
    @54
    cM
    c1
    caddc
    oveq1
    oveq1d
    #
    imaeq2d
    xpeq1d
    uneq12d
    oveq2d
    adantl
    csbied
    adantr
    eqtrd
    @129
    wph
    @19
    @100
    @65
    ovexd
    fvmptd
    fveq1d
    adantr
    @97
    @7
    @26
    wcel
    #
    @102
    @103
    wceq
    wph
    @23
    @26
    @7
    wph
    @23
    @5
    crn
    #
    @26
    @5
    @22
    imassrn
    wph
    @26
    @26
    @5
    wf
    #
    @135
    @26
    wss
    wph
    @75
    @136
    @81
    @26
    @26
    @5
    f1of
    syl
    @26
    @26
    @5
    frn
    syl
    syl5ss
    sselda
    #
    @97
    @26
    @26
    @20
    cc0
    caddc
    @26
    @19
    @100
    cvv
    cvv
    @7
    wph
    @19
    @26
    wfn
    #
    @24
    wph
    @19
    @37
    wcel
    #
    @138
    wph
    @77
    @139
    @80
    @4
    @37
    @34
    xp1st
    syl
    #
    @19
    @36
    @26
    elmapfn
    syl
    adantr
    wph
    @100
    @26
    wfn
    #
    @24
    wph
    @100
    @6
    @23
    cun
    #
    wfn
    #
    @141
    wph
    @98
    @6
    wfn
    #
    @99
    @23
    wfn
    #
    wa
    @6
    @23
    cin
    #
    c0
    wceq
    #
    @143
    @144
    @145
    c1
    cvv
    wcel
    #
    @144
    1ex
    @6
    c1
    cvv
    fnconstg
    ax-mp
    #
    cc0
    cvv
    wcel
    #
    @145
    c0ex
    @23
    cc0
    cvv
    fnconstg
    ax-mp
    #
    pm3.2i
    wph
    @5
    @93
    cima
    #
    @146
    c0
    wph
    @85
    @152
    @146
    wceq
    @86
    @2
    @22
    @5
    imain
    syl
    wph
    @152
    @5
    c0
    cima
    c0
    wph
    @93
    c0
    @5
    @96
    imaeq2d
    @5
    ima0
    syl6eq
    eqtr3d
    #
    @6
    @23
    @98
    @99
    fnun
    sylancr
    wph
    @142
    @26
    @100
    wph
    @142
    @5
    @89
    cima
    #
    @26
    @5
    @2
    @22
    imaundi
    wph
    @27
    @154
    @26
    wph
    @26
    @89
    @5
    @91
    imaeq2d
    @82
    eqtr3d
    syl5eqr
    fneq2d
    mpbid
    adantr
    @97
    c1
    cN
    cfz
    ovexd
    #
    @155
    @26
    inidm
    #
    @97
    @134
    wa
    @20
    eqidd
    @97
    @7
    @100
    cfv
    #
    cc0
    wceq
    @134
    @97
    @157
    @7
    @99
    cfv
    #
    cc0
    wph
    @147
    @24
    @157
    @158
    wceq
    #
    @153
    @144
    @145
    @147
    @24
    wa
    @159
    @149
    @151
    @6
    @23
    @98
    @99
    @7
    fvun2
    mp3an12
    sylan
    @24
    @158
    cc0
    wceq
    wph
    @23
    cc0
    @7
    c0ex
    fvconst2
    adantl
    eqtrd
    adantr
    ofval
    mpdan
    @97
    @20
    wph
    @24
    @134
    @20
    cc
    wcel
    @137
    wph
    @134
    wa
    #
    @20
    @160
    @20
    @36
    wcel
    @20
    cn0
    wcel
    wph
    @26
    @36
    @7
    @19
    wph
    @139
    @26
    @36
    @19
    wf
    @140
    @19
    @36
    @26
    elmapi
    syl
    ffvelrnda
    @20
    cK
    elfzonn0
    syl
    nn0cnd
    syldan
    addid1d
    3eqtrd
    syldan
    wph
    @8
    @18
    @14
    wceq
    @10
    wph
    @8
    wa
    #
    @18
    @7
    @12
    @3
    @57
    cxp
    #
    @1
    @22
    cima
    #
    @62
    cxp
    #
    cun
    #
    @65
    co
    #
    cfv
    #
    @14
    wph
    @18
    @167
    wceq
    @8
    wph
    @7
    @17
    @166
    wph
    vy
    @16
    vj
    @7
    cT
    c2nd
    cfv
    #
    clt
    wbr
    #
    @7
    @49
    cif
    #
    @12
    @1
    @55
    cima
    #
    @57
    cxp
    #
    @1
    @60
    cima
    #
    @62
    cxp
    #
    cun
    #
    @65
    co
    #
    csb
    #
    @166
    @45
    cF
    cvv
    wph
    @43
    cF
    vy
    @45
    @177
    cmpt
    #
    wceq
    #
    poimirlem12.2
    @43
    @42
    @179
    @69
    @179
    vt
    cT
    @41
    cS
    @46
    cT
    wceq
    #
    @68
    @178
    cF
    @180
    vy
    @45
    @67
    @177
    @180
    @67
    vj
    @170
    @66
    csb
    @177
    @180
    vj
    @50
    @170
    @66
    @180
    @48
    @169
    @7
    @49
    @180
    @47
    @168
    @7
    clt
    @46
    cT
    c2nd
    fveq2
    breq2d
    ifbid
    csbeq1d
    @180
    vj
    @170
    @66
    @176
    @180
    @52
    @12
    @64
    @175
    @65
    @180
    @51
    @0
    c1st
    @46
    cT
    c1st
    fveq2
    #
    fveq2d
    @180
    @58
    @172
    @63
    @174
    @180
    @56
    @171
    @57
    @180
    @53
    @1
    @55
    @180
    @51
    @0
    c2nd
    @181
    fveq2d
    #
    imaeq1d
    xpeq1d
    @180
    @61
    @173
    @62
    @180
    @53
    @1
    @60
    @182
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
    @120
    @177
    vj
    cM
    @176
    csb
    #
    @166
    @120
    vj
    @170
    cM
    @176
    @120
    @170
    @123
    cM
    @120
    @169
    @122
    @49
    cM
    @7
    @119
    wph
    @169
    @122
    wb
    #
    wph
    @119
    @168
    cc0
    wceq
    @184
    poimirlem11.3
    @7
    @16
    @168
    cc0
    clt
    breq12
    sylan2
    ancoms
    @126
    ifbieq2d
    @130
    eqtrd
    csbeq1d
    wph
    @183
    @166
    wceq
    @119
    wph
    vj
    cM
    @176
    @166
    @26
    poimirlem11.6
    @131
    @176
    @166
    wceq
    wph
    @131
    @175
    @165
    @12
    @65
    @131
    @172
    @162
    @174
    @164
    @131
    @171
    @3
    @57
    @131
    @55
    @2
    @1
    @132
    imaeq2d
    xpeq1d
    @131
    @173
    @163
    @62
    @131
    @60
    @22
    @1
    @133
    imaeq2d
    xpeq1d
    uneq12d
    oveq2d
    adantl
    csbied
    adantr
    eqtrd
    @129
    wph
    @12
    @165
    @65
    ovexd
    fvmptd
    fveq1d
    adantr
    @161
    @134
    @167
    @14
    wceq
    wph
    @3
    @26
    @7
    @73
    sselda
    #
    @161
    @26
    @26
    @13
    c1
    caddc
    @26
    @12
    @165
    cvv
    cvv
    @7
    wph
    @12
    @26
    wfn
    #
    @8
    wph
    @12
    @37
    wcel
    #
    @186
    wph
    @39
    @187
    @71
    @0
    @37
    @34
    xp1st
    syl
    #
    @12
    @36
    @26
    elmapfn
    syl
    adantr
    wph
    @165
    @26
    wfn
    #
    @8
    wph
    @165
    @3
    @163
    cun
    #
    wfn
    #
    @189
    wph
    @162
    @3
    wfn
    #
    @164
    @163
    wfn
    #
    wa
    @3
    @163
    cin
    #
    c0
    wceq
    #
    @191
    @192
    @193
    @148
    @192
    1ex
    @3
    c1
    cvv
    fnconstg
    ax-mp
    #
    @150
    @193
    c0ex
    @163
    cc0
    cvv
    fnconstg
    ax-mp
    #
    pm3.2i
    wph
    @1
    @93
    cima
    #
    @194
    c0
    wph
    @1
    ccnv
    wfun
    #
    @198
    @194
    wceq
    wph
    @31
    @199
    @72
    @31
    @26
    @26
    @1
    wfo
    #
    @199
    @26
    @26
    @1
    dff1o3
    simprbi
    syl
    @2
    @22
    @1
    imain
    syl
    wph
    @198
    @1
    c0
    cima
    c0
    wph
    @93
    c0
    @1
    @96
    imaeq2d
    @1
    ima0
    syl6eq
    eqtr3d
    #
    @3
    @163
    @162
    @164
    fnun
    sylancr
    wph
    @190
    @26
    @165
    wph
    @190
    @1
    @89
    cima
    #
    @26
    @1
    @2
    @22
    imaundi
    wph
    @1
    @26
    cima
    #
    @202
    @26
    wph
    @26
    @89
    @1
    @91
    imaeq2d
    wph
    @200
    @203
    @26
    wceq
    wph
    @31
    @200
    @72
    @26
    @26
    @1
    f1ofo
    syl
    @26
    @26
    @1
    foima
    syl
    eqtr3d
    syl5eqr
    fneq2d
    mpbid
    adantr
    @161
    c1
    cN
    cfz
    ovexd
    #
    @204
    @156
    @161
    @134
    wa
    @13
    eqidd
    @161
    @7
    @165
    cfv
    #
    c1
    wceq
    @134
    @161
    @205
    @7
    @162
    cfv
    #
    c1
    wph
    @195
    @8
    @205
    @206
    wceq
    #
    @201
    @192
    @193
    @195
    @8
    wa
    @207
    @196
    @197
    @3
    @163
    @162
    @164
    @7
    fvun1
    mp3an12
    sylan
    @8
    @206
    c1
    wceq
    wph
    @3
    c1
    @7
    1ex
    fvconst2
    adantl
    eqtrd
    adantr
    ofval
    mpdan
    eqtrd
    adantrr
    wph
    @20
    @13
    wceq
    @11
    wph
    @7
    @19
    @12
    wph
    @44
    cF
    cfv
    @26
    @57
    cxp
    cmin
    cof
    co
    @19
    @12
    wph
    vy
    vt
    cS
    cU
    vf
    vj
    cF
    cK
    cN
    poimir.0
    poimirlem22.s
    poimirlem22.1
    poimirlem11.4
    poimirlem11.5
    poimirlem10
    wph
    vy
    vt
    cS
    cT
    vf
    vj
    cF
    cK
    cN
    poimir.0
    poimirlem22.s
    poimirlem22.1
    poimirlem12.2
    poimirlem11.3
    poimirlem10
    eqtr3d
    fveq1d
    adantr
    3eqtr3d
    wph
    @8
    @15
    wn
    @10
    @161
    @14
    @13
    wph
    @8
    @134
    @14
    @13
    wne
    @185
    @160
    @13
    @14
    @160
    @13
    @160
    @13
    @36
    wcel
    @13
    cn0
    wcel
    wph
    @26
    @36
    @7
    @12
    wph
    @187
    @26
    @36
    @12
    wf
    @188
    @12
    @36
    @26
    elmapi
    syl
    ffvelrnda
    @13
    cK
    elfzonn0
    syl
    nn0red
    #
    @160
    @13
    @208
    ltp1d
    gtned
    syldan
    neneqd
    adantrr
    pm2.65da
    @8
    @9
    iman
    sylibr
    ssrdv
end
