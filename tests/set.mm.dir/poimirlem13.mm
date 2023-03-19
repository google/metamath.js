include "cv.mm"
include "c2nd.mm"
include "cfv.mm"
include "cc0.mm"
include "wceq.mm"
include "wa.mm"
include "weq.mm"
include "wi.mm"
include "wral.mm"
include "wrmo.mm"
include "wcel.mm"
include "c1st.mm"
include "c1.mm"
include "cmin.mm"
include "co.mm"
include "cfz.mm"
include "csn.mm"
include "cxp.mm"
include "cof.mm"
include "cn.mm"
include "ad2antrr.mm"
include "cmap.mm"
include "wf.mm"
include "simplrl.mm"
include "simprl.mm"
include "poimirlem10.mm"
include "simplrr.mm"
include "simprr.mm"
include "eqtr3d.mm"
include "wfn.mm"
include "wf1o.mm"
include "cab.mm"
include "cfzo.mm"
include "clt.mm"
include "wbr.mm"
include "caddc.mm"
include "cif.mm"
include "cima.mm"
include "cun.mm"
include "csb.mm"
include "cmpt.mm"
include "crab.mm"
include "elrabi.mm"
include "eleq2s.mm"
include "xp1st.mm"
include "syl.mm"
include "xp2nd.mm"
include "fvex.mm"
include "f1oeq1.mm"
include "elab.mm"
include "sylib.mm"
include "f1ofn.mm"
include "adantr.mm"
include "ad2antlr.mm"
include "adantl.mm"
include "cdif.mm"
include "eleq1.mm"
include "anbi2d.mm"
include "oveq2.mm"
include "imaeq2d.mm"
include "eqeq12d.mm"
include "imbi12d.mm"
include "ad3antrrr.mm"
include "simpl.mm"
include "ad3antlr.mm"
include "simpr.mm"
include "poimirlem11.mm"
include "eqssd.mm"
include "chvarv.mm"
include "wn.mm"
include "simpll.mm"
include "cle.mm"
include "cn0.mm"
include "wne.mm"
include "elfznn.mm"
include "nnm1nn0.mm"
include "cc.mm"
include "wb.mm"
include "nncnd.mm"
include "ax-1cn.mm"
include "subeq0.mm"
include "sylancl.mm"
include "necon3abid.mm"
include "biimpar.mm"
include "elnnne0.mm"
include "sylanbrc.mm"
include "cr.mm"
include "nn0red.mm"
include "nnred.mm"
include "lem1d.mm"
include "elfzle2.mm"
include "letrd.mm"
include "adantrr.mm"
include "cz.mm"
include "nnzd.mm"
include "fznn.mm"
include "mpbir2and.mm"
include "sylan.mm"
include "ovex.mm"
include "vtocl.mm"
include "syldan.mm"
include "expr.mm"
include "c0.mm"
include "ima0.mm"
include "eqtr4i.mm"
include "oveq1.mm"
include "1m1e0.mm"
include "syl6eq.mm"
include "oveq2d.mm"
include "fz10.mm"
include "3eqtr4a.mm"
include "pm2.61d2.mm"
include "difeq12d.mm"
include "fnsnfv.mm"
include "uncom.mm"
include "difeq1i.mm"
include "difun2.mm"
include "eqtri.mm"
include "cuz.mm"
include "nncn.mm"
include "npcan1.mm"
include "elnnuz.mm"
include "biimpi.mm"
include "eqeltrd.mm"
include "nn0zd.mm"
include "uzid.mm"
include "peano2uz.mm"
include "eqeltrrd.mm"
include "fzsplit2.mm"
include "syl2anc.mm"
include "oveq1d.mm"
include "nnz.mm"
include "fzsn.mm"
include "eqtrd.mm"
include "uneq2d.mm"
include "difeq1d.mm"
include "nnre.mm"
include "ltm1.mm"
include "peano2rem.mm"
include "ltnle.mm"
include "mpancom.mm"
include "mpbid.mm"
include "nsyl.mm"
include "cin.mm"
include "incom.mm"
include "eqeq1i.mm"
include "disjsn.mm"
include "disj3.mm"
include "3bitr3i.mm"
include "ccnv.mm"
include "wfun.mm"
include "wfo.mm"
include "dff1o3.mm"
include "simprbi.mm"
include "imadif.mm"
include "3eqtr2d.mm"
include "anbi1d.mm"
include "fveq2.mm"
include "fveq2d.mm"
include "fveq1d.mm"
include "sneqd.mm"
include "imaeq1d.mm"
include "3eqtr4d.mm"
include "sneqr.mm"
include "eqfnfvd.mm"
include "xpopth.mm"
include "syl2an.mm"
include "mpbi2and.mm"
include "eqtr3.mm"
include "ex.mm"
include "ralrimivva.mm"
include "eqeq1d.mm"
include "rmo4.mm"
include "sylibr.mm"

theorem poimirlem13
  let wph: wff ph
  let vy: setvar y
  let vz: setvar z
  let vt: setvar t
  let cS: class S
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
  let vi: setvar i
  let vq: setvar q
  let vu: setvar u
  let vw: setvar w
  let vx: setvar x
  let cM: class M
  let cT: class T
  let cU: class U
  let cV: class V
  let cB: class B
  assume poimir.0: |- ( ph -> N e. NN )
  assume poimirlem22.s: |- S = { t e. ( ( ( ( 0 ..^ K ) ^m ( 1 ... N ) ) X. { f | f : ( 1 ... N ) -1-1-onto-> ( 1 ... N ) } ) X. ( 0 ... N ) ) | F = ( y e. ( 0 ... ( N - 1 ) ) |-> [_ if ( y < ( 2nd ` t ) , y , ( y + 1 ) ) / j ]_ ( ( 1st ` ( 1st ` t ) ) oF + ( ( ( ( 2nd ` ( 1st ` t ) ) " ( 1 ... j ) ) X. { 1 } ) u. ( ( ( 2nd ` ( 1st ` t ) ) " ( ( j + 1 ) ... N ) ) X. { 0 } ) ) ) ) }
  assume poimirlem22.1: |- ( ph -> F : ( 0 ... ( N - 1 ) ) --> ( ( 0 ... K ) ^m ( 1 ... N ) ) )

  disjoint j t
  disjoint j y
  disjoint j z
  disjoint S j
  disjoint t y
  disjoint t z
  disjoint S t
  disjoint y z
  disjoint S y
  disjoint S z
  disjoint f j
  disjoint f t
  disjoint f y
  disjoint f z
  disjoint j t
  disjoint j y
  disjoint j z
  disjoint t y
  disjoint t z
  disjoint y z
  disjoint j ph
  disjoint ph y
  disjoint F j
  disjoint F y
  disjoint N j
  disjoint N y
  disjoint ph t
  disjoint K f
  disjoint K j
  disjoint K t
  disjoint N f
  disjoint N t
  disjoint ph z
  disjoint F f
  disjoint F t
  disjoint F z
  disjoint K z
  disjoint N z
  disjoint j k
  disjoint j m
  disjoint j n
  disjoint j p
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
  disjoint n ph
  disjoint F m
  disjoint F n
  disjoint M j
  disjoint M m
  disjoint M n
  disjoint M y
  disjoint N m
  disjoint N n
  disjoint T j
  disjoint T m
  disjoint T n
  disjoint T y
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
  disjoint T f
  disjoint T i
  disjoint T p
  disjoint U f
  disjoint U i
  disjoint U p
  disjoint F k
  disjoint F p
  disjoint F s
  disjoint T k
  disjoint T s
  disjoint T t
  disjoint T z
  disjoint U k
  disjoint U t
  assert |- ( ph -> E* z e. S ( 2nd ` z ) = 0 )

  proof
    wph
    vz
    cv
    #
    c2nd
    cfv
    #
    cc0
    wceq
    #
    vk
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
    vk
    weq
    #
    wi
    #
    vk
    cS
    wral
    vz
    cS
    wral
    @2
    vz
    cS
    wrmo
    wph
    @8
    vz
    vk
    cS
    cS
    wph
    @0
    cS
    wcel
    #
    @3
    cS
    wcel
    #
    wa
    #
    wa
    #
    @6
    @7
    @12
    @6
    wa
    #
    @0
    c1st
    cfv
    #
    @3
    c1st
    cfv
    #
    wceq
    #
    @1
    @4
    wceq
    #
    @7
    @13
    @14
    c1st
    cfv
    #
    @15
    c1st
    cfv
    #
    wceq
    #
    @14
    c2nd
    cfv
    #
    @15
    c2nd
    cfv
    #
    wceq
    #
    @16
    @13
    cN
    c1
    cmin
    co
    #
    cF
    cfv
    c1
    cN
    cfz
    co
    #
    c1
    csn
    #
    cxp
    cmin
    cof
    co
    @18
    @19
    @13
    vy
    vt
    cS
    @0
    vf
    vj
    cF
    cK
    cN
    wph
    cN
    cn
    wcel
    #
    @11
    @6
    poimir.0
    ad2antrr
    #
    poimirlem22.s
    wph
    cc0
    @24
    cfz
    co
    #
    cc0
    cK
    cfz
    co
    @25
    cmap
    co
    cF
    wf
    #
    @11
    @6
    poimirlem22.1
    ad2antrr
    #
    wph
    @9
    @10
    @6
    simplrl
    #
    @12
    @2
    @5
    simprl
    poimirlem10
    @13
    vy
    vt
    cS
    @3
    vf
    vj
    cF
    cK
    cN
    @28
    poimirlem22.s
    @31
    wph
    @9
    @10
    @6
    simplrr
    #
    @12
    @2
    @5
    simprr
    poimirlem10
    eqtr3d
    @13
    vn
    @25
    @21
    @22
    @11
    @21
    @25
    wfn
    #
    wph
    @6
    @9
    @34
    @10
    @9
    @25
    @25
    @21
    wf1o
    #
    @34
    @9
    @21
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
    @35
    @9
    @14
    cc0
    cK
    cfzo
    co
    @25
    cmap
    co
    #
    @38
    cxp
    #
    wcel
    #
    @39
    @9
    @0
    @41
    cc0
    cN
    cfz
    co
    #
    cxp
    #
    wcel
    #
    @42
    @45
    @0
    cF
    vy
    @29
    vj
    vy
    cv
    #
    vt
    cv
    #
    c2nd
    cfv
    clt
    wbr
    @46
    @46
    c1
    caddc
    co
    cif
    @47
    c1st
    cfv
    #
    c1st
    cfv
    @48
    c2nd
    cfv
    #
    c1
    vj
    cv
    #
    cfz
    co
    cima
    @26
    cxp
    @49
    @50
    c1
    caddc
    co
    cN
    cfz
    co
    cima
    cc0
    csn
    cxp
    cun
    caddc
    cof
    co
    csb
    cmpt
    wceq
    #
    vt
    @44
    crab
    #
    cS
    @51
    vt
    @0
    @44
    elrabi
    poimirlem22.s
    eleq2s
    #
    @0
    @41
    @43
    xp1st
    syl
    #
    @14
    @40
    @38
    xp2nd
    syl
    @37
    @35
    vf
    @21
    @14
    c2nd
    fvex
    @25
    @25
    @36
    @21
    f1oeq1
    elab
    sylib
    #
    @25
    @25
    @21
    f1ofn
    syl
    #
    adantr
    ad2antlr
    @11
    @22
    @25
    wfn
    #
    wph
    @6
    @10
    @57
    @9
    @10
    @25
    @25
    @22
    wf1o
    #
    @57
    @10
    @22
    @38
    wcel
    #
    @58
    @10
    @15
    @41
    wcel
    #
    @59
    @10
    @3
    @44
    wcel
    #
    @60
    @61
    @3
    @52
    cS
    @51
    vt
    @3
    @44
    elrabi
    poimirlem22.s
    eleq2s
    #
    @3
    @41
    @43
    xp1st
    syl
    #
    @15
    @40
    @38
    xp2nd
    syl
    @37
    @58
    vf
    @22
    @15
    c2nd
    fvex
    @25
    @25
    @36
    @22
    f1oeq1
    elab
    sylib
    @25
    @25
    @22
    f1ofn
    syl
    adantl
    ad2antlr
    @13
    vn
    cv
    #
    @25
    wcel
    #
    wa
    #
    @64
    @21
    cfv
    #
    csn
    #
    @64
    @22
    cfv
    #
    csn
    #
    wceq
    @67
    @69
    wceq
    @66
    @21
    c1
    @64
    cfz
    co
    #
    cima
    #
    @21
    c1
    @64
    c1
    cmin
    co
    #
    cfz
    co
    #
    cima
    #
    cdif
    #
    @22
    @71
    cima
    #
    @22
    @74
    cima
    #
    cdif
    #
    @68
    @70
    @66
    @72
    @77
    @75
    @78
    @13
    vm
    cv
    #
    @25
    wcel
    #
    wa
    #
    @21
    c1
    @80
    cfz
    co
    #
    cima
    #
    @22
    @83
    cima
    #
    wceq
    #
    wi
    #
    @66
    @72
    @77
    wceq
    #
    wi
    vm
    vn
    vm
    vn
    weq
    #
    @82
    @66
    @86
    @88
    @89
    @81
    @65
    @13
    @80
    @64
    @25
    eleq1
    anbi2d
    @89
    @84
    @72
    @85
    @77
    @89
    @83
    @71
    @21
    @80
    @64
    c1
    cfz
    oveq2
    #
    imaeq2d
    @89
    @83
    @71
    @22
    @90
    imaeq2d
    eqeq12d
    imbi12d
    @82
    @84
    @85
    @82
    vy
    vt
    cS
    @0
    @3
    vf
    vj
    cF
    cK
    @80
    cN
    wph
    @27
    @11
    @6
    @81
    poimir.0
    ad3antrrr
    #
    poimirlem22.s
    wph
    @30
    @11
    @6
    @81
    poimirlem22.1
    ad3antrrr
    #
    @11
    @9
    wph
    @6
    @81
    @9
    @10
    simpl
    ad3antlr
    #
    @12
    @2
    @5
    @81
    simplrl
    #
    @11
    @10
    wph
    @6
    @81
    @9
    @10
    simpr
    ad3antlr
    #
    @12
    @2
    @5
    @81
    simplrr
    #
    @13
    @81
    simpr
    #
    poimirlem11
    @82
    vy
    vt
    cS
    @3
    @0
    vf
    vj
    cF
    cK
    @80
    cN
    @91
    poimirlem22.s
    @92
    @95
    @96
    @93
    @94
    @97
    poimirlem11
    eqssd
    #
    chvarv
    @66
    @64
    c1
    wceq
    #
    @75
    @78
    wceq
    #
    @13
    @65
    @99
    wn
    #
    @100
    @13
    @65
    @101
    wa
    #
    @73
    @25
    wcel
    #
    @100
    @13
    wph
    @102
    @103
    wph
    @11
    @6
    simpll
    wph
    @102
    wa
    @103
    @73
    cn
    wcel
    #
    @73
    cN
    cle
    wbr
    #
    @102
    @104
    wph
    @102
    @73
    cn0
    wcel
    #
    @73
    cc0
    wne
    #
    @104
    @65
    @106
    @101
    @65
    @64
    cn
    wcel
    #
    @106
    @64
    cN
    elfznn
    #
    @64
    nnm1nn0
    #
    syl
    #
    adantr
    @65
    @107
    @101
    @65
    @99
    @73
    cc0
    @65
    @64
    cc
    wcel
    #
    c1
    cc
    wcel
    @73
    cc0
    wceq
    @99
    wb
    @65
    @64
    @109
    nncnd
    ax-1cn
    @64
    c1
    subeq0
    sylancl
    necon3abid
    biimpar
    @73
    elnnne0
    sylanbrc
    adantl
    wph
    @65
    @105
    @101
    wph
    @65
    wa
    @73
    @64
    cN
    @65
    @73
    cr
    wcel
    #
    wph
    @65
    @73
    @111
    nn0red
    adantl
    @65
    @64
    cr
    wcel
    #
    wph
    @65
    @64
    @109
    nnred
    #
    adantl
    wph
    cN
    cr
    wcel
    @65
    wph
    cN
    poimir.0
    nnred
    adantr
    @65
    @73
    @64
    cle
    wbr
    wph
    @65
    @64
    @115
    lem1d
    adantl
    @65
    @64
    cN
    cle
    wbr
    wph
    @64
    c1
    cN
    elfzle2
    adantl
    letrd
    adantrr
    wph
    @103
    @104
    @105
    wa
    wb
    #
    @102
    wph
    cN
    cz
    wcel
    @116
    wph
    cN
    poimir.0
    nnzd
    @73
    cN
    fznn
    syl
    adantr
    mpbir2and
    sylan
    @87
    @13
    @103
    wa
    #
    @100
    wi
    vm
    @73
    @64
    c1
    cmin
    ovex
    @80
    @73
    wceq
    #
    @82
    @117
    @86
    @100
    @118
    @81
    @103
    @13
    @80
    @73
    @25
    eleq1
    anbi2d
    @118
    @84
    @75
    @85
    @78
    @118
    @83
    @74
    @21
    @80
    @73
    c1
    cfz
    oveq2
    #
    imaeq2d
    @118
    @83
    @74
    @22
    @119
    imaeq2d
    eqeq12d
    imbi12d
    @98
    vtocl
    syldan
    expr
    @99
    @21
    c0
    cima
    #
    @22
    c0
    cima
    #
    @75
    @78
    @120
    c0
    @121
    @21
    ima0
    @22
    ima0
    eqtr4i
    @99
    @74
    c0
    @21
    @99
    @74
    c1
    cc0
    cfz
    co
    c0
    @99
    @73
    cc0
    c1
    cfz
    @99
    @73
    c1
    c1
    cmin
    co
    cc0
    @64
    c1
    c1
    cmin
    oveq1
    1m1e0
    syl6eq
    oveq2d
    fz10
    syl6eq
    #
    imaeq2d
    @99
    @74
    c0
    @22
    @122
    imaeq2d
    3eqtr4a
    pm2.61d2
    difeq12d
    @13
    @9
    @65
    @68
    @76
    wceq
    #
    @32
    @9
    @65
    wa
    #
    @68
    @21
    @64
    csn
    #
    cima
    #
    @21
    @71
    @74
    cdif
    #
    cima
    #
    @76
    @9
    @34
    @65
    @68
    @126
    wceq
    @56
    @25
    @64
    @21
    fnsnfv
    sylan
    @124
    @127
    @125
    @21
    @124
    @108
    @127
    @125
    wceq
    @65
    @108
    @9
    @109
    adantl
    @108
    @74
    @125
    cun
    #
    @74
    cdif
    #
    @125
    @74
    cdif
    #
    @127
    @125
    @130
    @125
    @74
    cun
    #
    @74
    cdif
    @131
    @129
    @132
    @74
    @74
    @125
    uncom
    difeq1i
    @125
    @74
    difun2
    eqtri
    @108
    @71
    @129
    @74
    @108
    @71
    @74
    @73
    c1
    caddc
    co
    #
    @64
    cfz
    co
    #
    cun
    #
    @129
    @108
    @133
    c1
    cuz
    cfv
    #
    wcel
    @64
    @73
    cuz
    cfv
    #
    wcel
    @71
    @135
    wceq
    @108
    @133
    @64
    @136
    @108
    @112
    @133
    @64
    wceq
    @64
    nncn
    @64
    npcan1
    syl
    #
    @108
    @64
    @136
    wcel
    @64
    elnnuz
    biimpi
    eqeltrd
    @108
    @133
    @64
    @137
    @138
    @108
    @73
    @137
    wcel
    #
    @133
    @137
    wcel
    @108
    @73
    cz
    wcel
    @139
    @108
    @73
    @110
    nn0zd
    @73
    uzid
    syl
    @73
    @73
    peano2uz
    syl
    eqeltrrd
    @73
    c1
    @64
    fzsplit2
    syl2anc
    @108
    @134
    @125
    @74
    @108
    @134
    @64
    @64
    cfz
    co
    #
    @125
    @108
    @133
    @64
    @64
    cfz
    @138
    oveq1d
    @108
    @64
    cz
    wcel
    @140
    @125
    wceq
    @64
    nnz
    @64
    fzsn
    syl
    eqtrd
    uneq2d
    eqtrd
    difeq1d
    @108
    @64
    @74
    wcel
    #
    wn
    #
    @125
    @131
    wceq
    #
    @108
    @114
    @142
    @64
    nnre
    @114
    @64
    @73
    cle
    wbr
    #
    @141
    @114
    @73
    @64
    clt
    wbr
    #
    @144
    wn
    #
    @64
    ltm1
    @113
    @114
    @145
    @146
    wb
    @64
    peano2rem
    @73
    @64
    ltnle
    mpancom
    mpbid
    @64
    c1
    @73
    elfzle2
    nsyl
    syl
    @74
    @125
    cin
    #
    c0
    wceq
    @125
    @74
    cin
    #
    c0
    wceq
    @142
    @143
    @147
    @148
    c0
    @74
    @125
    incom
    eqeq1i
    @74
    @64
    disjsn
    @125
    @74
    disj3
    3bitr3i
    sylib
    3eqtr4a
    syl
    imaeq2d
    @9
    @128
    @76
    wceq
    #
    @65
    @9
    @21
    ccnv
    wfun
    #
    @149
    @9
    @35
    @150
    @55
    @35
    @25
    @25
    @21
    wfo
    @150
    @25
    @25
    @21
    dff1o3
    simprbi
    syl
    @71
    @74
    @21
    imadif
    syl
    adantr
    3eqtr2d
    #
    sylan
    @13
    @10
    @65
    @70
    @79
    wceq
    #
    @33
    @124
    @123
    wi
    @10
    @65
    wa
    #
    @152
    wi
    vz
    vk
    @7
    @124
    @153
    @123
    @152
    @7
    @9
    @10
    @65
    @0
    @3
    cS
    eleq1
    anbi1d
    @7
    @68
    @70
    @76
    @79
    @7
    @67
    @69
    @7
    @64
    @21
    @22
    @7
    @14
    @15
    c2nd
    @0
    @3
    c1st
    fveq2
    fveq2d
    #
    fveq1d
    sneqd
    @7
    @72
    @77
    @75
    @78
    @7
    @21
    @22
    @71
    @154
    imaeq1d
    @7
    @21
    @22
    @74
    @154
    imaeq1d
    difeq12d
    eqeq12d
    imbi12d
    @151
    chvarv
    sylan
    3eqtr4d
    @67
    @69
    @64
    @21
    fvex
    sneqr
    syl
    eqfnfvd
    @11
    @20
    @23
    wa
    @16
    wb
    #
    wph
    @6
    @9
    @42
    @60
    @155
    @10
    @54
    @63
    @14
    @15
    @40
    @38
    @40
    @38
    xpopth
    syl2an
    ad2antlr
    mpbi2and
    @6
    @17
    @12
    @1
    @4
    cc0
    eqtr3
    adantl
    @11
    @16
    @17
    wa
    @7
    wb
    #
    wph
    @6
    @9
    @45
    @61
    @156
    @10
    @53
    @62
    @0
    @3
    @41
    @43
    @41
    @43
    xpopth
    syl2an
    ad2antlr
    mpbi2and
    ex
    ralrimivva
    @2
    @5
    vz
    vk
    cS
    @7
    @1
    @4
    cc0
    @0
    @3
    c2nd
    fveq2
    eqeq1d
    rmo4
    sylibr
end
