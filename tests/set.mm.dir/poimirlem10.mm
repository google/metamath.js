include "c1.mm"
include "cfz.mm"
include "co.mm"
include "cv.mm"
include "c1st.mm"
include "cfv.mm"
include "caddc.mm"
include "cmin.mm"
include "csn.mm"
include "cxp.mm"
include "cvv.mm"
include "ovexd.mm"
include "cc0.mm"
include "cmap.mm"
include "wcel.mm"
include "wfn.mm"
include "cn0.mm"
include "cn.mm"
include "nnm1nn0.mm"
include "syl.mm"
include "nn0fz0.mm"
include "sylib.mm"
include "ffvelrnd.mm"
include "elmapfn.mm"
include "1ex.mm"
include "fnconstg.mm"
include "mp1i.mm"
include "cfzo.mm"
include "wf1o.mm"
include "cab.mm"
include "c2nd.mm"
include "clt.mm"
include "wbr.mm"
include "cif.mm"
include "cima.mm"
include "cun.mm"
include "cof.mm"
include "csb.mm"
include "cmpt.mm"
include "wceq.mm"
include "crab.mm"
include "elrabi.mm"
include "eleq2s.mm"
include "xp1st.mm"
include "wa.mm"
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
include "wn.mm"
include "nn0ge0d.mm"
include "0red.mm"
include "nn0red.mm"
include "lenltd.mm"
include "mpbid.mm"
include "iffalsed.mm"
include "adantr.mm"
include "c0.mm"
include "oveq2.mm"
include "imaeq2d.mm"
include "wfo.mm"
include "xp2nd.mm"
include "fvex.mm"
include "f1oeq1.mm"
include "elab.mm"
include "f1ofo.mm"
include "foima.mm"
include "3syl.mm"
include "oveq1d.mm"
include "nnred.mm"
include "ltp1d.mm"
include "cz.mm"
include "nnzd.mm"
include "peano2zd.mm"
include "fzn.mm"
include "syl2anc.mm"
include "ima0.mm"
include "xpeq1i.mm"
include "0xp.mm"
include "eqtri.mm"
include "syl6eq.mm"
include "un0.mm"
include "oveq2d.mm"
include "csbied.mm"
include "fvmptd.mm"
include "fveq1d.mm"
include "inidm.mm"
include "eqidd.mm"
include "fvconst2.mm"
include "adantl.mm"
include "ofval.mm"
include "wf.mm"
include "elmapi.mm"
include "ffvelrnda.mm"
include "elfzonn0.mm"
include "nn0cnd.mm"
include "pncan1.mm"
include "offveq.mm"

theorem poimirlem10
  let wph: wff ph
  let vy: setvar y
  let vt: setvar t
  let cS: class S
  let cT: class T
  let vf: setvar f
  let vj: setvar j
  let cF: class F
  let cK: class K
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
  let cM: class M
  let cU: class U
  let cV: class V
  let cB: class B
  assume poimir.0: |- ( ph -> N e. NN )
  assume poimirlem22.s: |- S = { t e. ( ( ( ( 0 ..^ K ) ^m ( 1 ... N ) ) X. { f | f : ( 1 ... N ) -1-1-onto-> ( 1 ... N ) } ) X. ( 0 ... N ) ) | F = ( y e. ( 0 ... ( N - 1 ) ) |-> [_ if ( y < ( 2nd ` t ) , y , ( y + 1 ) ) / j ]_ ( ( 1st ` ( 1st ` t ) ) oF + ( ( ( ( 2nd ` ( 1st ` t ) ) " ( 1 ... j ) ) X. { 1 } ) u. ( ( ( 2nd ` ( 1st ` t ) ) " ( ( j + 1 ) ... N ) ) X. { 0 } ) ) ) ) }
  assume poimirlem22.1: |- ( ph -> F : ( 0 ... ( N - 1 ) ) --> ( ( 0 ... K ) ^m ( 1 ... N ) ) )
  assume poimirlem12.2: |- ( ph -> T e. S )
  assume poimirlem11.3: |- ( ph -> ( 2nd ` T ) = 0 )

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
  disjoint N j
  disjoint N y
  disjoint T j
  disjoint T y
  disjoint ph t
  disjoint K f
  disjoint K j
  disjoint K t
  disjoint N f
  disjoint N t
  disjoint T f
  disjoint F f
  disjoint F t
  disjoint T t
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
  disjoint M j
  disjoint M m
  disjoint M n
  disjoint M y
  disjoint N m
  disjoint N n
  disjoint T m
  disjoint T n
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
  disjoint M f
  disjoint M i
  disjoint M k
  disjoint M p
  disjoint M s
  disjoint M t
  disjoint N i
  disjoint N k
  disjoint N p
  disjoint N s
  disjoint T i
  disjoint T p
  disjoint U f
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
  disjoint U t
  assert |- ( ph -> ( ( F ` ( N - 1 ) ) oF - ( ( 1 ... N ) X. { 1 } ) ) = ( 1st ` ( 1st ` T ) ) )

  proof
    wph
    vn
    c1
    cN
    cfz
    co
    #
    vn
    cv
    #
    cT
    c1st
    cfv
    #
    c1st
    cfv
    #
    cfv
    #
    c1
    caddc
    co
    #
    c1
    cmin
    cN
    c1
    cmin
    co
    #
    cF
    cfv
    #
    @0
    c1
    csn
    #
    cxp
    #
    @3
    cvv
    wph
    c1
    cN
    cfz
    ovexd
    #
    wph
    @7
    cc0
    cK
    cfz
    co
    #
    @0
    cmap
    co
    #
    wcel
    @7
    @0
    wfn
    wph
    cc0
    @6
    cfz
    co
    #
    @12
    @6
    cF
    poimirlem22.1
    wph
    @6
    cn0
    wcel
    #
    @6
    @13
    wcel
    wph
    cN
    cn
    wcel
    @14
    poimir.0
    cN
    nnm1nn0
    syl
    #
    @6
    nn0fz0
    sylib
    #
    ffvelrnd
    @7
    @11
    @0
    elmapfn
    syl
    c1
    cvv
    wcel
    @9
    @0
    wfn
    wph
    1ex
    @0
    c1
    cvv
    fnconstg
    mp1i
    #
    wph
    @3
    cc0
    cK
    cfzo
    co
    #
    @0
    cmap
    co
    #
    wcel
    #
    @3
    @0
    wfn
    wph
    @2
    @19
    @0
    @0
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
    wcel
    #
    @20
    wph
    cT
    @24
    cc0
    cN
    cfz
    co
    #
    cxp
    #
    wcel
    #
    @25
    wph
    cT
    cS
    wcel
    #
    @28
    poimirlem12.2
    @28
    cT
    cF
    vy
    @13
    vj
    vy
    cv
    #
    vt
    cv
    #
    c2nd
    cfv
    #
    clt
    wbr
    #
    @30
    @30
    c1
    caddc
    co
    #
    cif
    #
    @31
    c1st
    cfv
    #
    c1st
    cfv
    #
    @36
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
    @8
    cxp
    #
    @38
    @39
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
    @27
    crab
    cS
    @53
    vt
    cT
    @27
    elrabi
    poimirlem22.s
    eleq2s
    syl
    cT
    @24
    @26
    xp1st
    syl
    #
    @2
    @19
    @23
    xp1st
    syl
    #
    @3
    @18
    @0
    elmapfn
    syl
    #
    wph
    @1
    @0
    wcel
    #
    wa
    #
    @1
    @7
    cfv
    #
    @1
    @3
    @9
    @49
    co
    #
    cfv
    #
    @5
    wph
    @59
    @61
    wceq
    @57
    wph
    @1
    @7
    @60
    wph
    vy
    @6
    vj
    @30
    cT
    c2nd
    cfv
    #
    clt
    wbr
    #
    @30
    @34
    cif
    #
    @3
    @2
    c2nd
    cfv
    #
    @40
    cima
    #
    @8
    cxp
    #
    @65
    @44
    cima
    #
    @46
    cxp
    #
    cun
    #
    @49
    co
    #
    csb
    #
    @60
    @13
    cF
    cvv
    wph
    @29
    cF
    vy
    @13
    @72
    cmpt
    #
    wceq
    #
    poimirlem12.2
    @29
    @28
    @74
    @53
    @74
    vt
    cT
    @27
    cS
    @31
    cT
    wceq
    #
    @52
    @73
    cF
    @75
    vy
    @13
    @51
    @72
    @75
    @51
    vj
    @64
    @50
    csb
    @72
    @75
    vj
    @35
    @64
    @50
    @75
    @33
    @63
    @30
    @34
    @75
    @32
    @62
    @30
    clt
    @31
    cT
    c2nd
    fveq2
    breq2d
    ifbid
    csbeq1d
    @75
    vj
    @64
    @50
    @71
    @75
    @37
    @3
    @48
    @70
    @49
    @75
    @36
    @2
    c1st
    @31
    cT
    c1st
    fveq2
    #
    fveq2d
    @75
    @42
    @67
    @47
    @69
    @75
    @41
    @66
    @8
    @75
    @38
    @65
    @40
    @75
    @36
    @2
    c2nd
    @76
    fveq2d
    #
    imaeq1d
    xpeq1d
    @75
    @45
    @68
    @46
    @75
    @38
    @65
    @44
    @77
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
    @30
    @6
    wceq
    #
    wa
    #
    @72
    vj
    cN
    @71
    csb
    #
    @60
    @79
    vj
    @64
    cN
    @71
    @79
    @64
    @6
    cc0
    clt
    wbr
    #
    @30
    cN
    cif
    #
    cN
    @79
    @63
    @81
    @34
    cN
    @30
    @78
    wph
    @63
    @81
    wb
    #
    wph
    @78
    @62
    cc0
    wceq
    @83
    poimirlem11.3
    @30
    @6
    @62
    cc0
    clt
    breq12
    sylan2
    ancoms
    @78
    wph
    @34
    @6
    c1
    caddc
    co
    #
    cN
    @30
    @6
    c1
    caddc
    oveq1
    wph
    cN
    cc
    wcel
    @84
    cN
    wceq
    wph
    cN
    poimir.0
    nncnd
    cN
    npcan1
    syl
    sylan9eqr
    ifbieq2d
    wph
    @82
    cN
    wceq
    @78
    wph
    @81
    @30
    cN
    wph
    cc0
    @6
    cle
    wbr
    @81
    wn
    wph
    @6
    @15
    nn0ge0d
    wph
    cc0
    @6
    wph
    0red
    wph
    @6
    @15
    nn0red
    lenltd
    mpbid
    iffalsed
    adantr
    eqtrd
    csbeq1d
    wph
    @80
    @60
    wceq
    @78
    wph
    vj
    cN
    @71
    @60
    cn
    poimir.0
    wph
    @39
    cN
    wceq
    #
    wa
    #
    @70
    @9
    @3
    @49
    @86
    @70
    @9
    c0
    cun
    @9
    @86
    @67
    @9
    @69
    c0
    @86
    @66
    @0
    @8
    @85
    wph
    @66
    @65
    @0
    cima
    #
    @0
    @85
    @40
    @0
    @65
    @39
    cN
    c1
    cfz
    oveq2
    imaeq2d
    wph
    @0
    @0
    @65
    wf1o
    #
    @0
    @0
    @65
    wfo
    @87
    @0
    wceq
    wph
    @65
    @23
    wcel
    #
    @88
    wph
    @25
    @89
    @54
    @2
    @19
    @23
    xp2nd
    syl
    @22
    @88
    vf
    @65
    @2
    c2nd
    fvex
    @0
    @0
    @21
    @65
    f1oeq1
    elab
    sylib
    @0
    @0
    @65
    f1ofo
    @0
    @0
    @65
    foima
    3syl
    sylan9eqr
    xpeq1d
    @86
    @69
    @65
    c0
    cima
    #
    @46
    cxp
    #
    c0
    @86
    @68
    @90
    @46
    @86
    @44
    c0
    @65
    @85
    wph
    @44
    cN
    c1
    caddc
    co
    #
    cN
    cfz
    co
    #
    c0
    @85
    @43
    @92
    cN
    cfz
    @39
    cN
    c1
    caddc
    oveq1
    oveq1d
    wph
    cN
    @92
    clt
    wbr
    #
    @93
    c0
    wceq
    #
    wph
    cN
    wph
    cN
    poimir.0
    nnred
    ltp1d
    wph
    @92
    cz
    wcel
    cN
    cz
    wcel
    @94
    @95
    wb
    wph
    cN
    wph
    cN
    poimir.0
    nnzd
    #
    peano2zd
    @96
    @92
    cN
    fzn
    syl2anc
    mpbid
    sylan9eqr
    imaeq2d
    xpeq1d
    @91
    c0
    @46
    cxp
    c0
    @90
    c0
    @46
    @65
    ima0
    xpeq1i
    @46
    0xp
    eqtri
    syl6eq
    uneq12d
    @9
    un0
    syl6eq
    oveq2d
    csbied
    adantr
    eqtrd
    @16
    wph
    @3
    @9
    @49
    ovexd
    fvmptd
    fveq1d
    adantr
    wph
    @0
    @0
    @4
    c1
    caddc
    @0
    @3
    @9
    cvv
    cvv
    @1
    @56
    @17
    @10
    @10
    @0
    inidm
    @58
    @4
    eqidd
    @57
    @1
    @9
    cfv
    c1
    wceq
    wph
    @0
    c1
    @1
    1ex
    fvconst2
    adantl
    #
    ofval
    eqtrd
    @97
    @58
    @4
    cc
    wcel
    @5
    c1
    cmin
    co
    @4
    wceq
    @58
    @4
    @58
    @4
    @18
    wcel
    @4
    cn0
    wcel
    wph
    @0
    @18
    @1
    @3
    wph
    @20
    @0
    @18
    @3
    wf
    @55
    @3
    @18
    @0
    elmapi
    syl
    ffvelrnda
    @4
    cK
    elfzonn0
    syl
    nn0cnd
    @4
    pncan1
    syl
    offveq
end
