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
include "cdif.mm"
include "eldif.mm"
include "crn.mm"
include "imassrn.mm"
include "wf1o.mm"
include "wf.mm"
include "wss.mm"
include "cab.mm"
include "cc0.mm"
include "cfzo.mm"
include "cmap.mm"
include "cxp.mm"
include "cmin.mm"
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
include "xp1st.mm"
include "3syl.mm"
include "xp2nd.mm"
include "syl.mm"
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
include "cuz.mm"
include "cn.mm"
include "cn0.mm"
include "elfznn0.mm"
include "nn0p1nn.mm"
include "nnuz.mm"
include "syl6eleq.mm"
include "cc.mm"
include "nncnd.mm"
include "npcan1.mm"
include "elfzuz3.mm"
include "peano2uz.mm"
include "eqeltrrd.mm"
include "fzsplit2.mm"
include "syl2anc.mm"
include "uncom.mm"
include "syl6eq.mm"
include "difeq1d.mm"
include "cin.mm"
include "c0.mm"
include "incom.mm"
include "nn0red.mm"
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
include "breq1.mm"
include "id.mm"
include "ifbieq1d.mm"
include "cr.mm"
include "nnred.mm"
include "peano2rem.mm"
include "cle.mm"
include "elfzle2.mm"
include "ltm1d.mm"
include "lelttrd.mm"
include "breqtrrd.mm"
include "iftrued.mm"
include "sylan9eqr.mm"
include "oveq2.mm"
include "oveq1.mm"
include "oveq1d.mm"
include "oveq2d.mm"
include "adantl.mm"
include "csbied.mm"
include "adantr.mm"
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
include "mpbid.mm"
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
include "addid1d.mm"
include "syldan.mm"
include "3eqtrd.mm"
include "fvun1.mm"
include "adantrr.mm"
include "nngt0d.mm"
include "poimirlem5.mm"
include "3eqtr3d.mm"
include "wne.mm"
include "gtned.mm"
include "neneqd.mm"
include "pm2.65da.mm"
include "iman.mm"
include "sylibr.mm"
include "ssrdv.mm"

theorem poimirlem12
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
  assume poimirlem12.3: |- ( ph -> ( 2nd ` T ) = N )
  assume poimirlem12.4: |- ( ph -> U e. S )
  assume poimirlem12.5: |- ( ph -> ( 2nd ` U ) = N )
  assume poimirlem12.6: |- ( ph -> M e. ( 0 ... ( N - 1 ) ) )

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
    @17
    @19
    wceq
    @11
    wph
    @7
    @3
    @6
    cdif
    #
    wcel
    @23
    @7
    @3
    @6
    eldif
    wph
    @24
    @22
    @7
    wph
    @24
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
    @22
    wph
    @3
    @26
    @6
    wph
    @3
    @25
    @26
    wph
    @3
    @1
    crn
    #
    @25
    @1
    @2
    imassrn
    wph
    @25
    @25
    @1
    wf1o
    #
    @25
    @25
    @1
    wf
    @28
    @25
    wss
    wph
    @1
    @25
    @25
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
    @29
    wph
    @0
    cc0
    cK
    cfzo
    co
    #
    @25
    cmap
    co
    #
    @32
    cxp
    #
    wcel
    #
    @33
    wph
    cT
    cS
    wcel
    #
    cT
    @36
    cc0
    cN
    cfz
    co
    #
    cxp
    #
    wcel
    #
    @37
    poimirlem12.2
    @41
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
    @44
    c1st
    cfv
    #
    c1st
    cfv
    #
    @49
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
    @51
    @52
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
    @40
    crab
    #
    cS
    @67
    vt
    cT
    @40
    elrabi
    poimirlem22.s
    eleq2s
    cT
    @36
    @39
    xp1st
    3syl
    #
    @0
    @35
    @32
    xp2nd
    syl
    @31
    @29
    vf
    @1
    @0
    c2nd
    fvex
    @25
    @25
    @30
    @1
    f1oeq1
    elab
    sylib
    #
    @25
    @25
    @1
    f1of
    @25
    @25
    @1
    frn
    3syl
    syl5ss
    #
    wph
    @25
    @25
    @5
    wf1o
    #
    @25
    @25
    @5
    wfo
    #
    @26
    @25
    wceq
    wph
    @5
    @32
    wcel
    #
    @72
    wph
    @4
    @36
    wcel
    #
    @74
    wph
    cU
    cS
    wcel
    #
    cU
    @40
    wcel
    #
    @75
    poimirlem12.4
    @77
    cU
    @68
    cS
    @67
    vt
    cU
    @40
    elrabi
    poimirlem22.s
    eleq2s
    cU
    @36
    @39
    xp1st
    3syl
    #
    @4
    @35
    @32
    xp2nd
    syl
    @31
    @72
    vf
    @5
    @4
    c2nd
    fvex
    @25
    @25
    @30
    @5
    f1oeq1
    elab
    sylib
    #
    @25
    @25
    @5
    f1ofo
    @25
    @25
    @5
    foima
    3syl
    #
    sseqtr4d
    ssdifd
    wph
    @5
    @25
    @2
    cdif
    #
    cima
    #
    @27
    @22
    wph
    @72
    @5
    ccnv
    wfun
    #
    @82
    @27
    wceq
    @79
    @72
    @73
    @83
    @25
    @25
    @5
    dff1o3
    simprbi
    #
    @25
    @2
    @5
    imadif
    3syl
    wph
    @81
    @21
    @5
    wph
    @21
    @2
    cun
    #
    @2
    cdif
    @21
    @2
    cdif
    #
    @81
    @21
    @21
    @2
    difun2
    wph
    @25
    @85
    @2
    wph
    @25
    @2
    @21
    cun
    #
    @85
    wph
    @20
    c1
    cuz
    cfv
    #
    wcel
    cN
    cM
    cuz
    cfv
    #
    wcel
    @25
    @87
    wceq
    wph
    @20
    cn
    @88
    wph
    cM
    @43
    wcel
    #
    cM
    cn0
    wcel
    #
    @20
    cn
    wcel
    poimirlem12.6
    cM
    @42
    elfznn0
    #
    cM
    nn0p1nn
    3syl
    nnuz
    syl6eleq
    wph
    @42
    c1
    caddc
    co
    #
    cN
    @89
    wph
    cN
    cc
    wcel
    @93
    cN
    wceq
    wph
    cN
    poimir.0
    nncnd
    cN
    npcan1
    syl
    wph
    @90
    @42
    @89
    wcel
    @93
    @89
    wcel
    poimirlem12.6
    cM
    cc0
    @42
    elfzuz3
    cM
    @42
    peano2uz
    3syl
    eqeltrrd
    cM
    c1
    cN
    fzsplit2
    syl2anc
    #
    @2
    @21
    uncom
    syl6eq
    difeq1d
    wph
    @21
    @2
    cin
    #
    c0
    wceq
    @21
    @86
    wceq
    wph
    @95
    @2
    @21
    cin
    #
    c0
    @21
    @2
    incom
    wph
    cM
    @20
    clt
    wbr
    @96
    c0
    wceq
    wph
    cM
    wph
    cM
    wph
    @90
    @91
    poimirlem12.6
    @92
    syl
    nn0red
    #
    ltp1d
    c1
    cM
    @20
    cN
    fzdisj
    syl
    #
    syl5eq
    @21
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
    @23
    wa
    #
    @17
    @7
    @18
    @6
    @55
    cxp
    #
    @22
    @60
    cxp
    #
    cun
    #
    @63
    co
    #
    cfv
    #
    @19
    cc0
    caddc
    co
    #
    @19
    wph
    @17
    @104
    wceq
    @23
    wph
    @7
    @16
    @103
    wph
    vy
    cM
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
    @47
    cif
    #
    @18
    @5
    @53
    cima
    #
    @55
    cxp
    #
    @5
    @58
    cima
    #
    @60
    cxp
    #
    cun
    #
    @63
    co
    #
    csb
    #
    @103
    @43
    cF
    cvv
    wph
    @76
    cF
    vy
    @43
    @115
    cmpt
    #
    wceq
    #
    poimirlem12.4
    @76
    @77
    @117
    @67
    @117
    vt
    cU
    @40
    cS
    @44
    cU
    wceq
    #
    @66
    @116
    cF
    @118
    vy
    @43
    @65
    @115
    @118
    @65
    vj
    @108
    @64
    csb
    @115
    @118
    vj
    @48
    @108
    @64
    @118
    @46
    @107
    @7
    @47
    @118
    @45
    @106
    @7
    clt
    @44
    cU
    c2nd
    fveq2
    breq2d
    ifbid
    csbeq1d
    @118
    vj
    @108
    @64
    @114
    @118
    @50
    @18
    @62
    @113
    @63
    @118
    @49
    @4
    c1st
    @44
    cU
    c1st
    fveq2
    #
    fveq2d
    @118
    @56
    @110
    @61
    @112
    @118
    @54
    @109
    @55
    @118
    @51
    @5
    @53
    @118
    @49
    @4
    c2nd
    @119
    fveq2d
    #
    imaeq1d
    xpeq1d
    @118
    @59
    @111
    @60
    @118
    @51
    @5
    @58
    @120
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
    cM
    wceq
    #
    wa
    #
    @115
    vj
    cM
    @114
    csb
    #
    @103
    @122
    vj
    @108
    cM
    @114
    @121
    wph
    @108
    cM
    @106
    clt
    wbr
    #
    cM
    @47
    cif
    cM
    @121
    @107
    @124
    @7
    cM
    @47
    @7
    cM
    @106
    clt
    breq1
    @121
    id
    #
    ifbieq1d
    wph
    @124
    cM
    @47
    wph
    cM
    cN
    @106
    clt
    wph
    cM
    @42
    cN
    @97
    wph
    cN
    cr
    wcel
    @42
    cr
    wcel
    wph
    cN
    poimir.0
    nnred
    #
    cN
    peano2rem
    syl
    @126
    wph
    @90
    cM
    @42
    cle
    wbr
    poimirlem12.6
    cM
    cc0
    @42
    elfzle2
    syl
    wph
    cN
    @126
    ltm1d
    lelttrd
    #
    poimirlem12.5
    breqtrrd
    iftrued
    sylan9eqr
    csbeq1d
    wph
    @123
    @103
    wceq
    @121
    wph
    vj
    cM
    @114
    @103
    @43
    poimirlem12.6
    @52
    cM
    wceq
    #
    @114
    @103
    wceq
    wph
    @128
    @113
    @102
    @18
    @63
    @128
    @110
    @100
    @112
    @101
    @128
    @109
    @6
    @55
    @128
    @53
    @2
    @5
    @52
    cM
    c1
    cfz
    oveq2
    #
    imaeq2d
    xpeq1d
    @128
    @111
    @22
    @60
    @128
    @58
    @21
    @5
    @128
    @57
    @20
    cN
    cfz
    @52
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
    poimirlem12.6
    wph
    @18
    @102
    @63
    ovexd
    fvmptd
    fveq1d
    adantr
    @99
    @7
    @25
    wcel
    #
    @104
    @105
    wceq
    wph
    @22
    @25
    @7
    wph
    @22
    @5
    crn
    #
    @25
    @5
    @21
    imassrn
    wph
    @72
    @25
    @25
    @5
    wf
    @132
    @25
    wss
    @79
    @25
    @25
    @5
    f1of
    @25
    @25
    @5
    frn
    3syl
    syl5ss
    sselda
    #
    @99
    @25
    @25
    @19
    cc0
    caddc
    @25
    @18
    @102
    cvv
    cvv
    @7
    wph
    @18
    @25
    wfn
    #
    @23
    wph
    @75
    @18
    @35
    wcel
    #
    @134
    @78
    @4
    @35
    @32
    xp1st
    #
    @18
    @34
    @25
    elmapfn
    3syl
    adantr
    wph
    @102
    @25
    wfn
    #
    @23
    wph
    @102
    @6
    @22
    cun
    #
    wfn
    #
    @137
    wph
    @100
    @6
    wfn
    #
    @101
    @22
    wfn
    #
    wa
    @6
    @22
    cin
    #
    c0
    wceq
    #
    @139
    @140
    @141
    c1
    cvv
    wcel
    #
    @140
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
    @141
    c0ex
    @22
    cc0
    cvv
    fnconstg
    ax-mp
    #
    pm3.2i
    wph
    @5
    @96
    cima
    #
    @142
    c0
    wph
    @72
    @83
    @148
    @142
    wceq
    @79
    @84
    @2
    @21
    @5
    imain
    3syl
    wph
    @148
    @5
    c0
    cima
    c0
    wph
    @96
    c0
    @5
    @98
    imaeq2d
    @5
    ima0
    syl6eq
    eqtr3d
    #
    @6
    @22
    @100
    @101
    fnun
    sylancr
    wph
    @138
    @25
    @102
    wph
    @138
    @5
    @87
    cima
    #
    @25
    @5
    @2
    @21
    imaundi
    wph
    @26
    @150
    @25
    wph
    @25
    @87
    @5
    @94
    imaeq2d
    @80
    eqtr3d
    syl5eqr
    fneq2d
    mpbid
    adantr
    @99
    c1
    cN
    cfz
    ovexd
    #
    @151
    @25
    inidm
    #
    @99
    @131
    wa
    @19
    eqidd
    @99
    @7
    @102
    cfv
    #
    cc0
    wceq
    @131
    @99
    @153
    @7
    @101
    cfv
    #
    cc0
    wph
    @143
    @23
    @153
    @154
    wceq
    #
    @149
    @140
    @141
    @143
    @23
    wa
    @155
    @145
    @147
    @6
    @22
    @100
    @101
    @7
    fvun2
    mp3an12
    sylan
    @23
    @154
    cc0
    wceq
    wph
    @22
    cc0
    @7
    c0ex
    fvconst2
    adantl
    eqtrd
    adantr
    ofval
    mpdan
    wph
    @23
    @131
    @105
    @19
    wceq
    @133
    wph
    @131
    wa
    #
    @19
    @156
    @19
    @156
    @19
    @34
    wcel
    @19
    cn0
    wcel
    wph
    @25
    @34
    @7
    @18
    wph
    @75
    @135
    @25
    @34
    @18
    wf
    @78
    @136
    @18
    @34
    @25
    elmapi
    3syl
    ffvelrnda
    @19
    cK
    elfzonn0
    syl
    nn0cnd
    addid1d
    syldan
    3eqtrd
    syldan
    wph
    @8
    @17
    @14
    wceq
    @10
    wph
    @8
    wa
    #
    @17
    @7
    @12
    @3
    @55
    cxp
    #
    @1
    @21
    cima
    #
    @60
    cxp
    #
    cun
    #
    @63
    co
    #
    cfv
    #
    @14
    wph
    @17
    @163
    wceq
    @8
    wph
    @7
    @16
    @162
    wph
    vy
    cM
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
    @47
    cif
    #
    @12
    @1
    @53
    cima
    #
    @55
    cxp
    #
    @1
    @58
    cima
    #
    @60
    cxp
    #
    cun
    #
    @63
    co
    #
    csb
    #
    @162
    @43
    cF
    cvv
    wph
    @38
    cF
    vy
    @43
    @173
    cmpt
    #
    wceq
    #
    poimirlem12.2
    @38
    @41
    @175
    @67
    @175
    vt
    cT
    @40
    cS
    @44
    cT
    wceq
    #
    @66
    @174
    cF
    @176
    vy
    @43
    @65
    @173
    @176
    @65
    vj
    @166
    @64
    csb
    @173
    @176
    vj
    @48
    @166
    @64
    @176
    @46
    @165
    @7
    @47
    @176
    @45
    @164
    @7
    clt
    @44
    cT
    c2nd
    fveq2
    breq2d
    ifbid
    csbeq1d
    @176
    vj
    @166
    @64
    @172
    @176
    @50
    @12
    @62
    @171
    @63
    @176
    @49
    @0
    c1st
    @44
    cT
    c1st
    fveq2
    #
    fveq2d
    @176
    @56
    @168
    @61
    @170
    @176
    @54
    @167
    @55
    @176
    @51
    @1
    @53
    @176
    @49
    @0
    c2nd
    @177
    fveq2d
    #
    imaeq1d
    xpeq1d
    @176
    @59
    @169
    @60
    @176
    @51
    @1
    @58
    @178
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
    @122
    @173
    vj
    cM
    @172
    csb
    #
    @162
    @122
    vj
    @166
    cM
    @172
    @121
    wph
    @166
    cM
    @164
    clt
    wbr
    #
    cM
    @47
    cif
    cM
    @121
    @165
    @180
    @7
    cM
    @47
    @7
    cM
    @164
    clt
    breq1
    @125
    ifbieq1d
    wph
    @180
    cM
    @47
    wph
    cM
    cN
    @164
    clt
    @127
    poimirlem12.3
    breqtrrd
    iftrued
    sylan9eqr
    csbeq1d
    wph
    @179
    @162
    wceq
    @121
    wph
    vj
    cM
    @172
    @162
    @43
    poimirlem12.6
    @128
    @172
    @162
    wceq
    wph
    @128
    @171
    @161
    @12
    @63
    @128
    @168
    @158
    @170
    @160
    @128
    @167
    @3
    @55
    @128
    @53
    @2
    @1
    @129
    imaeq2d
    xpeq1d
    @128
    @169
    @159
    @60
    @128
    @58
    @21
    @1
    @130
    imaeq2d
    xpeq1d
    uneq12d
    oveq2d
    adantl
    csbied
    adantr
    eqtrd
    poimirlem12.6
    wph
    @12
    @161
    @63
    ovexd
    fvmptd
    fveq1d
    adantr
    @157
    @131
    @163
    @14
    wceq
    wph
    @3
    @25
    @7
    @71
    sselda
    #
    @157
    @25
    @25
    @13
    c1
    caddc
    @25
    @12
    @161
    cvv
    cvv
    @7
    wph
    @12
    @25
    wfn
    #
    @8
    wph
    @37
    @12
    @35
    wcel
    #
    @182
    @69
    @0
    @35
    @32
    xp1st
    #
    @12
    @34
    @25
    elmapfn
    3syl
    adantr
    wph
    @161
    @25
    wfn
    #
    @8
    wph
    @161
    @3
    @159
    cun
    #
    wfn
    #
    @185
    wph
    @158
    @3
    wfn
    #
    @160
    @159
    wfn
    #
    wa
    @3
    @159
    cin
    #
    c0
    wceq
    #
    @187
    @188
    @189
    @144
    @188
    1ex
    @3
    c1
    cvv
    fnconstg
    ax-mp
    #
    @146
    @189
    c0ex
    @159
    cc0
    cvv
    fnconstg
    ax-mp
    #
    pm3.2i
    wph
    @1
    @96
    cima
    #
    @190
    c0
    wph
    @29
    @1
    ccnv
    wfun
    #
    @194
    @190
    wceq
    @70
    @29
    @25
    @25
    @1
    wfo
    #
    @195
    @25
    @25
    @1
    dff1o3
    simprbi
    @2
    @21
    @1
    imain
    3syl
    wph
    @194
    @1
    c0
    cima
    c0
    wph
    @96
    c0
    @1
    @98
    imaeq2d
    @1
    ima0
    syl6eq
    eqtr3d
    #
    @3
    @159
    @158
    @160
    fnun
    sylancr
    wph
    @186
    @25
    @161
    wph
    @186
    @1
    @87
    cima
    #
    @25
    @1
    @2
    @21
    imaundi
    wph
    @1
    @25
    cima
    #
    @198
    @25
    wph
    @25
    @87
    @1
    @94
    imaeq2d
    wph
    @29
    @196
    @199
    @25
    wceq
    @70
    @25
    @25
    @1
    f1ofo
    @25
    @25
    @1
    foima
    3syl
    eqtr3d
    syl5eqr
    fneq2d
    mpbid
    adantr
    @157
    c1
    cN
    cfz
    ovexd
    #
    @200
    @152
    @157
    @131
    wa
    @13
    eqidd
    @157
    @7
    @161
    cfv
    #
    c1
    wceq
    @131
    @157
    @201
    @7
    @158
    cfv
    #
    c1
    wph
    @191
    @8
    @201
    @202
    wceq
    #
    @197
    @188
    @189
    @191
    @8
    wa
    @203
    @192
    @193
    @3
    @159
    @158
    @160
    @7
    fvun1
    mp3an12
    sylan
    @8
    @202
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
    @19
    @13
    wceq
    @11
    wph
    @7
    @18
    @12
    wph
    cc0
    cF
    cfv
    @18
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
    poimirlem12.4
    wph
    cc0
    cN
    @106
    clt
    wph
    cN
    poimir.0
    nngt0d
    #
    poimirlem12.5
    breqtrrd
    poimirlem5
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
    poimirlem12.2
    wph
    cc0
    cN
    @164
    clt
    @204
    poimirlem12.3
    breqtrrd
    poimirlem5
    eqtr3d
    fveq1d
    adantr
    3eqtr3d
    wph
    @8
    @15
    wn
    @10
    @157
    @14
    @13
    wph
    @8
    @131
    @14
    @13
    wne
    @181
    @156
    @13
    @14
    @156
    @13
    @156
    @13
    @34
    wcel
    @13
    cn0
    wcel
    wph
    @25
    @34
    @7
    @12
    wph
    @37
    @183
    @25
    @34
    @12
    wf
    @69
    @184
    @12
    @34
    @25
    elmapi
    3syl
    ffvelrnda
    @13
    cK
    elfzonn0
    syl
    nn0red
    #
    @156
    @13
    @205
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
