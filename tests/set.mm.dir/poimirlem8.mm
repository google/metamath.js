include "c1.mm"
include "cfz.mm"
include "co.mm"
include "c2nd.mm"
include "cfv.mm"
include "caddc.mm"
include "cpr.mm"
include "cdif.mm"
include "c1st.mm"
include "cres.mm"
include "wfn.mm"
include "wss.mm"
include "wf1o.mm"
include "cv.mm"
include "cab.mm"
include "wcel.mm"
include "cc0.mm"
include "cfzo.mm"
include "cmap.mm"
include "cxp.mm"
include "cmin.mm"
include "clt.mm"
include "wbr.mm"
include "cif.mm"
include "cima.mm"
include "csn.mm"
include "cun.mm"
include "cof.mm"
include "csb.mm"
include "cmpt.mm"
include "wceq.mm"
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
include "f1ofn.mm"
include "difss.mm"
include "fnssres.mm"
include "sylancl.mm"
include "wa.mm"
include "wo.mm"
include "fzp1elp1.mm"
include "cc.mm"
include "nncnd.mm"
include "npcan1.mm"
include "oveq2d.mm"
include "eleqtrd.mm"
include "fzsplit.mm"
include "difeq1d.mm"
include "difundir.mm"
include "cuz.mm"
include "cn.mm"
include "elfznn.mm"
include "nnuz.mm"
include "syl6eleq.mm"
include "eqeltrd.mm"
include "cz.mm"
include "nnzd.mm"
include "peano2zm.mm"
include "uzid.mm"
include "peano2uz.mm"
include "3syl.mm"
include "eqeltrrd.mm"
include "fzsplit2.mm"
include "syl2anc.mm"
include "oveq1d.mm"
include "fzpr.mm"
include "eqtrd.mm"
include "uneq2d.mm"
include "cin.mm"
include "wn.mm"
include "cle.mm"
include "nnred.mm"
include "ltm1d.mm"
include "zred.mm"
include "ltnled.mm"
include "mpbid.mm"
include "elfzle2.mm"
include "nsyl.mm"
include "difsn.mm"
include "cr.mm"
include "peano2re.mm"
include "ltp1d.mm"
include "lttrd.mm"
include "ineq12d.mm"
include "difun2.mm"
include "df-pr.mm"
include "difeq2i.mm"
include "difundi.mm"
include "3eqtrri.mm"
include "inidm.mm"
include "3eqtr3g.mm"
include "elfzle1.mm"
include "eqtr2i.mm"
include "uneq12d.mm"
include "syl5eq.mm"
include "eleq2d.mm"
include "elun.mm"
include "syl6bb.mm"
include "biimpa.mm"
include "wne.mm"
include "crio.mm"
include "wrmo.mm"
include "fveq2.mm"
include "breq2d.mm"
include "ifbid.mm"
include "csbeq1d.mm"
include "fveq2d.mm"
include "imaeq1d.mm"
include "xpeq1d.mm"
include "oveq12d.mm"
include "csbeq2dv.mm"
include "mpteq2dv.mm"
include "eqeq2d.mm"
include "elrab2.mm"
include "simprbi.mm"
include "wf.mm"
include "elmapi.mm"
include "elfzoelz.mm"
include "ssriv.mm"
include "fss.mm"
include "poimirlem1.mm"
include "adantr.mm"
include "eldifsn.mm"
include "biimpri.mm"
include "sylan.mm"
include "poimirlem2.mm"
include "ex.mm"
include "necon1bd.mm"
include "mpd.mm"
include "biimpar.mm"
include "simpr.mm"
include "poimirlem6.mm"
include "syldan.mm"
include "eqtr3d.mm"
include "c2.mm"
include "poimirlem7.mm"
include "jaodan.mm"
include "fvres.mm"
include "adantl.mm"
include "3eqtr4d.mm"
include "eqfnfvd.mm"

theorem poimirlem8
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
  let cV: class V
  let cB: class B
  assume poimir.0: |- ( ph -> N e. NN )
  assume poimirlem22.s: |- S = { t e. ( ( ( ( 0 ..^ K ) ^m ( 1 ... N ) ) X. { f | f : ( 1 ... N ) -1-1-onto-> ( 1 ... N ) } ) X. ( 0 ... N ) ) | F = ( y e. ( 0 ... ( N - 1 ) ) |-> [_ if ( y < ( 2nd ` t ) , y , ( y + 1 ) ) / j ]_ ( ( 1st ` ( 1st ` t ) ) oF + ( ( ( ( 2nd ` ( 1st ` t ) ) " ( 1 ... j ) ) X. { 1 } ) u. ( ( ( 2nd ` ( 1st ` t ) ) " ( ( j + 1 ) ... N ) ) X. { 0 } ) ) ) ) }
  assume poimirlem9.1: |- ( ph -> T e. S )
  assume poimirlem9.2: |- ( ph -> ( 2nd ` T ) e. ( 1 ... ( N - 1 ) ) )
  assume poimirlem9.3: |- ( ph -> U e. S )

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
  disjoint U j
  disjoint U y
  disjoint ph t
  disjoint K f
  disjoint K j
  disjoint K t
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
  disjoint M j
  disjoint M m
  disjoint M n
  disjoint M y
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
  assert |- ( ph -> ( ( 2nd ` ( 1st ` U ) ) |` ( ( 1 ... N ) \ { ( 2nd ` T ) , ( ( 2nd ` T ) + 1 ) } ) ) = ( ( 2nd ` ( 1st ` T ) ) |` ( ( 1 ... N ) \ { ( 2nd ` T ) , ( ( 2nd ` T ) + 1 ) } ) ) )

  proof
    wph
    vk
    c1
    cN
    cfz
    co
    #
    cT
    c2nd
    cfv
    #
    @1
    c1
    caddc
    co
    #
    cpr
    #
    cdif
    #
    cU
    c1st
    cfv
    #
    c2nd
    cfv
    #
    @4
    cres
    #
    cT
    c1st
    cfv
    #
    c2nd
    cfv
    #
    @4
    cres
    #
    wph
    @6
    @0
    wfn
    #
    @4
    @0
    wss
    #
    @7
    @4
    wfn
    wph
    @0
    @0
    @6
    wf1o
    #
    @11
    wph
    @6
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
    wcel
    #
    @13
    wph
    @5
    cc0
    cK
    cfzo
    co
    #
    @0
    cmap
    co
    #
    @16
    cxp
    #
    wcel
    #
    @17
    wph
    cU
    @20
    cc0
    cN
    cfz
    co
    #
    cxp
    #
    wcel
    #
    @21
    wph
    cU
    cS
    wcel
    #
    @24
    poimirlem9.3
    @24
    cU
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
    @28
    @28
    c1
    caddc
    co
    #
    cif
    #
    @29
    c1st
    cfv
    #
    c1st
    cfv
    #
    @34
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
    @36
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
    vt
    @23
    crab
    #
    cS
    @51
    vt
    cU
    @23
    elrabi
    poimirlem22.s
    eleq2s
    syl
    #
    cU
    @20
    @22
    xp1st
    syl
    #
    @5
    @19
    @16
    xp2nd
    syl
    @15
    @13
    vf
    @6
    @5
    c2nd
    fvex
    @0
    @0
    @14
    @6
    f1oeq1
    elab
    sylib
    #
    @0
    @0
    @6
    f1ofn
    syl
    @0
    @3
    difss
    #
    @0
    @4
    @6
    fnssres
    sylancl
    wph
    @9
    @0
    wfn
    #
    @12
    @10
    @4
    wfn
    wph
    @0
    @0
    @9
    wf1o
    #
    @57
    wph
    @9
    @16
    wcel
    #
    @58
    wph
    @8
    @20
    wcel
    #
    @59
    wph
    cT
    @23
    wcel
    #
    @60
    wph
    cT
    cS
    wcel
    #
    @61
    poimirlem9.1
    @61
    cT
    @52
    cS
    @51
    vt
    cT
    @23
    elrabi
    poimirlem22.s
    eleq2s
    syl
    cT
    @20
    @22
    xp1st
    syl
    #
    @8
    @19
    @16
    xp2nd
    syl
    @15
    @58
    vf
    @9
    @8
    c2nd
    fvex
    @0
    @0
    @14
    @9
    f1oeq1
    elab
    sylib
    #
    @0
    @0
    @9
    f1ofn
    syl
    @56
    @0
    @4
    @9
    fnssres
    sylancl
    wph
    vk
    cv
    #
    @4
    wcel
    #
    wa
    @65
    @6
    cfv
    #
    @65
    @9
    cfv
    #
    @65
    @7
    cfv
    #
    @65
    @10
    cfv
    #
    wph
    @66
    @65
    c1
    @1
    c1
    cmin
    co
    #
    cfz
    co
    #
    wcel
    #
    @65
    @2
    c1
    caddc
    co
    #
    cN
    cfz
    co
    #
    wcel
    #
    wo
    #
    @67
    @68
    wceq
    #
    wph
    @66
    @77
    wph
    @66
    @65
    @72
    @75
    cun
    #
    wcel
    @77
    wph
    @4
    @79
    @65
    wph
    @4
    c1
    @2
    cfz
    co
    #
    @75
    cun
    #
    @3
    cdif
    #
    @79
    wph
    @0
    @81
    @3
    wph
    @2
    @0
    wcel
    @0
    @81
    wceq
    wph
    @2
    c1
    @26
    c1
    caddc
    co
    #
    cfz
    co
    #
    @0
    wph
    @1
    c1
    @26
    cfz
    co
    #
    wcel
    #
    @2
    @84
    wcel
    poimirlem9.2
    @1
    c1
    @26
    fzp1elp1
    syl
    wph
    @83
    cN
    c1
    cfz
    wph
    cN
    cc
    wcel
    @83
    cN
    wceq
    wph
    cN
    poimir.0
    nncnd
    cN
    npcan1
    syl
    oveq2d
    eleqtrd
    @2
    c1
    cN
    fzsplit
    syl
    difeq1d
    wph
    @82
    @80
    @3
    cdif
    #
    @75
    @3
    cdif
    #
    cun
    @79
    @80
    @75
    @3
    difundir
    wph
    @87
    @72
    @88
    @75
    wph
    @87
    @72
    @3
    cun
    #
    @3
    cdif
    #
    @72
    wph
    @80
    @89
    @3
    wph
    @80
    @72
    @71
    c1
    caddc
    co
    #
    @2
    cfz
    co
    #
    cun
    #
    @89
    wph
    @91
    c1
    cuz
    cfv
    #
    wcel
    @2
    @71
    cuz
    cfv
    #
    wcel
    #
    @80
    @93
    wceq
    wph
    @91
    @1
    @94
    wph
    @1
    cc
    wcel
    @91
    @1
    wceq
    wph
    @1
    wph
    @86
    @1
    cn
    wcel
    poimirlem9.2
    @1
    @26
    elfznn
    syl
    #
    nncnd
    @1
    npcan1
    syl
    #
    wph
    @1
    cn
    @94
    @97
    nnuz
    syl6eleq
    eqeltrd
    wph
    @1
    @95
    wcel
    @96
    wph
    @91
    @1
    @95
    @98
    wph
    @71
    cz
    wcel
    #
    @71
    @95
    wcel
    @91
    @95
    wcel
    wph
    @1
    cz
    wcel
    #
    @99
    wph
    @1
    @97
    nnzd
    #
    @1
    peano2zm
    syl
    #
    @71
    uzid
    @71
    @71
    peano2uz
    3syl
    eqeltrrd
    @71
    @1
    peano2uz
    syl
    @71
    c1
    @2
    fzsplit2
    syl2anc
    wph
    @92
    @3
    @72
    wph
    @92
    @1
    @2
    cfz
    co
    #
    @3
    wph
    @91
    @1
    @2
    cfz
    @98
    oveq1d
    wph
    @100
    @103
    @3
    wceq
    @101
    @1
    fzpr
    syl
    eqtrd
    uneq2d
    eqtrd
    difeq1d
    wph
    @72
    @1
    csn
    #
    cdif
    #
    @72
    @2
    csn
    #
    cdif
    #
    cin
    #
    @72
    @72
    cin
    @90
    @72
    wph
    @105
    @72
    @107
    @72
    wph
    @1
    @72
    wcel
    #
    wn
    @105
    @72
    wceq
    wph
    @1
    @71
    cle
    wbr
    #
    @109
    wph
    @71
    @1
    clt
    wbr
    @110
    wn
    wph
    @1
    wph
    @1
    @97
    nnred
    #
    ltm1d
    #
    wph
    @71
    @1
    wph
    @71
    @102
    zred
    #
    @111
    ltnled
    mpbid
    @1
    c1
    @71
    elfzle2
    nsyl
    @1
    @72
    difsn
    syl
    wph
    @2
    @72
    wcel
    #
    wn
    @107
    @72
    wceq
    wph
    @2
    @71
    cle
    wbr
    #
    @114
    wph
    @71
    @2
    clt
    wbr
    @115
    wn
    wph
    @71
    @1
    @2
    @113
    @111
    wph
    @1
    cr
    wcel
    @2
    cr
    wcel
    #
    @111
    @1
    peano2re
    syl
    #
    @112
    wph
    @1
    @111
    ltp1d
    #
    lttrd
    wph
    @71
    @2
    @113
    @117
    ltnled
    mpbid
    @2
    c1
    @71
    elfzle2
    nsyl
    @2
    @72
    difsn
    syl
    ineq12d
    @90
    @72
    @3
    cdif
    @72
    @104
    @106
    cun
    #
    cdif
    @108
    @72
    @3
    difun2
    @3
    @119
    @72
    @1
    @2
    df-pr
    #
    difeq2i
    @72
    @104
    @106
    difundi
    3eqtrri
    @72
    inidm
    3eqtr3g
    eqtrd
    wph
    @75
    @104
    cdif
    #
    @75
    @106
    cdif
    #
    cin
    #
    @75
    @75
    cin
    @88
    @75
    wph
    @121
    @75
    @122
    @75
    wph
    @1
    @75
    wcel
    #
    wn
    @121
    @75
    wceq
    wph
    @74
    @1
    cle
    wbr
    #
    @124
    wph
    @1
    @74
    clt
    wbr
    @125
    wn
    wph
    @1
    @2
    @74
    @111
    @117
    wph
    @116
    @74
    cr
    wcel
    @117
    @2
    peano2re
    syl
    #
    @118
    wph
    @2
    @117
    ltp1d
    #
    lttrd
    wph
    @1
    @74
    @111
    @126
    ltnled
    mpbid
    @1
    @74
    cN
    elfzle1
    nsyl
    @1
    @75
    difsn
    syl
    wph
    @2
    @75
    wcel
    #
    wn
    @122
    @75
    wceq
    wph
    @74
    @2
    cle
    wbr
    #
    @128
    wph
    @2
    @74
    clt
    wbr
    @129
    wn
    @127
    wph
    @2
    @74
    @117
    @126
    ltnled
    mpbid
    @2
    @74
    cN
    elfzle1
    nsyl
    @2
    @75
    difsn
    syl
    ineq12d
    @88
    @75
    @119
    cdif
    @123
    @3
    @119
    @75
    @120
    difeq2i
    @75
    @104
    @106
    difundi
    eqtr2i
    @75
    inidm
    3eqtr3g
    uneq12d
    syl5eq
    eqtrd
    eleq2d
    @65
    @72
    @75
    elun
    syl6bb
    biimpa
    wph
    @73
    @78
    @76
    wph
    @73
    wa
    #
    vn
    cv
    #
    @65
    c1
    cmin
    co
    cF
    cfv
    cfv
    #
    @131
    @65
    cF
    cfv
    cfv
    wne
    vn
    @0
    crio
    #
    @67
    @68
    wph
    @73
    @65
    c1
    cU
    c2nd
    cfv
    #
    c1
    cmin
    co
    #
    cfz
    co
    #
    wcel
    #
    @133
    @67
    wceq
    wph
    @137
    @73
    wph
    @136
    @72
    @65
    wph
    @135
    @71
    c1
    cfz
    wph
    @134
    @1
    c1
    cmin
    wph
    @131
    @71
    cF
    cfv
    cfv
    @131
    @1
    cF
    cfv
    cfv
    wne
    vn
    @0
    wrmo
    #
    wn
    @134
    @1
    wceq
    wph
    vy
    @8
    c1st
    cfv
    #
    @9
    vj
    vn
    cF
    @1
    cN
    poimir.0
    wph
    @62
    cF
    vy
    @27
    vj
    @28
    @1
    clt
    wbr
    #
    @28
    @32
    cif
    #
    @139
    @9
    @38
    cima
    #
    @40
    cxp
    #
    @9
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
    poimirlem9.1
    @62
    @61
    @150
    @51
    @150
    vt
    cT
    @23
    cS
    @29
    cT
    wceq
    #
    @50
    @149
    cF
    @151
    vy
    @27
    @49
    @148
    @151
    @49
    vj
    @141
    @48
    csb
    @148
    @151
    vj
    @33
    @141
    @48
    @151
    @31
    @140
    @28
    @32
    @151
    @30
    @1
    @28
    clt
    @29
    cT
    c2nd
    fveq2
    breq2d
    ifbid
    csbeq1d
    @151
    vj
    @141
    @48
    @147
    @151
    @35
    @139
    @46
    @146
    @47
    @151
    @34
    @8
    c1st
    @29
    cT
    c1st
    fveq2
    #
    fveq2d
    @151
    @41
    @143
    @45
    @145
    @151
    @39
    @142
    @40
    @151
    @36
    @9
    @38
    @151
    @34
    @8
    c2nd
    @152
    fveq2d
    #
    imaeq1d
    xpeq1d
    @151
    @43
    @144
    @44
    @151
    @36
    @9
    @42
    @153
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
    @0
    @18
    @139
    wf
    #
    @18
    cz
    wss
    #
    @0
    cz
    @139
    wf
    wph
    @139
    @19
    wcel
    #
    @154
    wph
    @60
    @156
    @63
    @8
    @19
    @16
    xp1st
    syl
    @139
    @18
    @0
    elmapi
    syl
    vn
    @18
    cz
    @131
    cc0
    cK
    elfzoelz
    ssriv
    #
    @0
    @18
    cz
    @139
    fss
    sylancl
    @64
    poimirlem9.2
    poimirlem1
    wph
    @138
    @134
    @1
    wph
    @134
    @1
    wne
    #
    @138
    wph
    @158
    wa
    vy
    @5
    c1st
    cfv
    #
    @6
    vj
    vn
    cF
    @134
    cN
    @1
    wph
    cN
    cn
    wcel
    #
    @158
    poimir.0
    adantr
    wph
    cF
    vy
    @27
    vj
    @28
    @134
    clt
    wbr
    #
    @28
    @32
    cif
    #
    @159
    @6
    @38
    cima
    #
    @40
    cxp
    #
    @6
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
    @158
    wph
    @25
    @171
    poimirlem9.3
    @25
    @24
    @171
    @51
    @171
    vt
    cU
    @23
    cS
    @29
    cU
    wceq
    #
    @50
    @170
    cF
    @172
    vy
    @27
    @49
    @169
    @172
    @49
    vj
    @162
    @48
    csb
    @169
    @172
    vj
    @33
    @162
    @48
    @172
    @31
    @161
    @28
    @32
    @172
    @30
    @134
    @28
    clt
    @29
    cU
    c2nd
    fveq2
    breq2d
    ifbid
    csbeq1d
    @172
    vj
    @162
    @48
    @168
    @172
    @35
    @159
    @46
    @167
    @47
    @172
    @34
    @5
    c1st
    @29
    cU
    c1st
    fveq2
    #
    fveq2d
    @172
    @41
    @164
    @45
    @166
    @172
    @39
    @163
    @40
    @172
    @36
    @6
    @38
    @172
    @34
    @5
    c2nd
    @173
    fveq2d
    #
    imaeq1d
    xpeq1d
    @172
    @43
    @165
    @44
    @172
    @36
    @6
    @42
    @174
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
    adantr
    wph
    @0
    cz
    @159
    wf
    #
    @158
    wph
    @0
    @18
    @159
    wf
    #
    @155
    @175
    wph
    @159
    @19
    wcel
    #
    @176
    wph
    @21
    @177
    @54
    @5
    @19
    @16
    xp1st
    syl
    @159
    @18
    @0
    elmapi
    syl
    @157
    @0
    @18
    cz
    @159
    fss
    sylancl
    adantr
    wph
    @13
    @158
    @55
    adantr
    wph
    @86
    @158
    poimirlem9.2
    adantr
    wph
    @134
    @22
    wcel
    #
    @158
    @134
    @22
    @104
    cdif
    wcel
    #
    wph
    @24
    @178
    @53
    cU
    @20
    @22
    xp2nd
    syl
    @179
    @178
    @158
    wa
    @134
    @22
    @1
    eldifsn
    biimpri
    sylan
    poimirlem2
    ex
    necon1bd
    mpd
    #
    oveq1d
    oveq2d
    eleq2d
    biimpar
    wph
    @137
    wa
    vy
    vt
    cS
    cU
    vf
    vj
    vn
    cF
    cK
    @65
    cN
    wph
    @160
    @137
    poimir.0
    adantr
    poimirlem22.s
    wph
    @25
    @137
    poimirlem9.3
    adantr
    wph
    @134
    @85
    wcel
    #
    @137
    wph
    @134
    @1
    @85
    @180
    poimirlem9.2
    eqeltrd
    #
    adantr
    wph
    @137
    simpr
    poimirlem6
    syldan
    @130
    vy
    vt
    cS
    cT
    vf
    vj
    vn
    cF
    cK
    @65
    cN
    wph
    @160
    @73
    poimir.0
    adantr
    poimirlem22.s
    wph
    @62
    @73
    poimirlem9.1
    adantr
    wph
    @86
    @73
    poimirlem9.2
    adantr
    wph
    @73
    simpr
    poimirlem6
    eqtr3d
    wph
    @76
    wa
    #
    @131
    @65
    c2
    cmin
    co
    cF
    cfv
    cfv
    @132
    wne
    vn
    @0
    crio
    #
    @67
    @68
    wph
    @76
    @65
    @134
    c1
    caddc
    co
    #
    c1
    caddc
    co
    #
    cN
    cfz
    co
    #
    wcel
    #
    @184
    @67
    wceq
    wph
    @188
    @76
    wph
    @187
    @75
    @65
    wph
    @186
    @74
    cN
    cfz
    wph
    @185
    @2
    c1
    caddc
    wph
    @134
    @1
    c1
    caddc
    @180
    oveq1d
    oveq1d
    oveq1d
    eleq2d
    biimpar
    wph
    @188
    wa
    vy
    vt
    cS
    cU
    vf
    vj
    vn
    cF
    cK
    @65
    cN
    wph
    @160
    @188
    poimir.0
    adantr
    poimirlem22.s
    wph
    @25
    @188
    poimirlem9.3
    adantr
    wph
    @181
    @188
    @182
    adantr
    wph
    @188
    simpr
    poimirlem7
    syldan
    @183
    vy
    vt
    cS
    cT
    vf
    vj
    vn
    cF
    cK
    @65
    cN
    wph
    @160
    @76
    poimir.0
    adantr
    poimirlem22.s
    wph
    @62
    @76
    poimirlem9.1
    adantr
    wph
    @86
    @76
    poimirlem9.2
    adantr
    wph
    @76
    simpr
    poimirlem7
    eqtr3d
    jaodan
    syldan
    @66
    @69
    @67
    wceq
    wph
    @65
    @4
    @6
    fvres
    adantl
    @66
    @70
    @68
    wceq
    wph
    @65
    @4
    @9
    fvres
    adantl
    3eqtr4d
    eqfnfvd
end
