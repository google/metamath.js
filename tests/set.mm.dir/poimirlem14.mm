include "cv.mm"
include "c2nd.mm"
include "cfv.mm"
include "wceq.mm"
include "wa.mm"
include "weq.mm"
include "wi.mm"
include "wral.mm"
include "wrmo.mm"
include "wcel.mm"
include "c1st.mm"
include "cc0.mm"
include "cn.mm"
include "ad2antrr.mm"
include "simplrl.mm"
include "clt.mm"
include "wbr.mm"
include "nngt0d.mm"
include "breq2.mm"
include "biimparc.mm"
include "sylan.mm"
include "ad2ant2r.mm"
include "poimirlem5.mm"
include "simplrr.mm"
include "ad2ant2rl.mm"
include "eqtr3d.mm"
include "c1.mm"
include "cfz.mm"
include "co.mm"
include "wfn.mm"
include "wf1o.mm"
include "cab.mm"
include "cfzo.mm"
include "cmap.mm"
include "cxp.mm"
include "cmin.mm"
include "caddc.mm"
include "cif.mm"
include "cima.mm"
include "csn.mm"
include "cun.mm"
include "cof.mm"
include "csb.mm"
include "cmpt.mm"
include "crab.mm"
include "elrabi.mm"
include "eleq2s.mm"
include "xp1st.mm"
include "xp2nd.mm"
include "3syl.mm"
include "fvex.mm"
include "f1oeq1.mm"
include "elab.mm"
include "sylib.mm"
include "f1ofn.mm"
include "syl.mm"
include "adantr.mm"
include "ad2antlr.mm"
include "adantl.mm"
include "cdif.mm"
include "simpllr.mm"
include "oveq2.mm"
include "imaeq2d.mm"
include "wfo.mm"
include "f1ofo.mm"
include "foima.mm"
include "sylan9eqr.mm"
include "adantlr.mm"
include "adantll.mm"
include "eqtr4d.mm"
include "wne.mm"
include "simpll.mm"
include "wn.mm"
include "wo.mm"
include "cuz.mm"
include "wb.mm"
include "elnnuz.mm"
include "fzm1.mm"
include "anbi1d.mm"
include "biimpa.mm"
include "df-ne.mm"
include "anbi2i.mm"
include "pm5.61.mm"
include "bitri.mm"
include "wss.mm"
include "1eluzge0.mm"
include "fzss1.mm"
include "ax-mp.mm"
include "sseli.mm"
include "eleq1.mm"
include "anbi2d.mm"
include "eqeq12d.mm"
include "imbi12d.mm"
include "ad3antrrr.mm"
include "wf.mm"
include "simpl.mm"
include "ad3antlr.mm"
include "simpr.mm"
include "poimirlem12.mm"
include "eqssd.mm"
include "chvarv.mm"
include "syldan.mm"
include "anassrs.mm"
include "pm2.61dane.mm"
include "cz.mm"
include "elfzelz.mm"
include "nnzd.mm"
include "elfzm1b.mm"
include "syl2anr.mm"
include "mpbid.mm"
include "ovex.mm"
include "vtocl.mm"
include "difeq12d.mm"
include "fnsnfv.mm"
include "elfznn.mm"
include "uncom.mm"
include "difeq1i.mm"
include "difun2.mm"
include "eqtri.mm"
include "cc.mm"
include "nncn.mm"
include "npcan1.mm"
include "biimpi.mm"
include "eqeltrd.mm"
include "nnm1nn0.mm"
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
include "cr.mm"
include "nnre.mm"
include "cle.mm"
include "ltm1.mm"
include "peano2rem.mm"
include "ltnle.mm"
include "mpancom.mm"
include "elfzle2.mm"
include "nsyl.mm"
include "cin.mm"
include "c0.mm"
include "incom.mm"
include "eqeq1i.mm"
include "disjsn.mm"
include "disj3.mm"
include "3bitr3i.mm"
include "3eqtr4a.mm"
include "ccnv.mm"
include "wfun.mm"
include "dff1o3.mm"
include "simprbi.mm"
include "imadif.mm"
include "3eqtr2d.mm"
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

theorem poimirlem14
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
  assert |- ( ph -> E* z e. S ( 2nd ` z ) = N )

  proof
    wph
    vz
    cv
    #
    c2nd
    cfv
    #
    cN
    wceq
    #
    vk
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
    cc0
    cF
    cfv
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
    @9
    @10
    @6
    simplrl
    #
    wph
    @2
    cc0
    @1
    clt
    wbr
    #
    @11
    @5
    wph
    cc0
    cN
    clt
    wbr
    #
    @2
    @27
    wph
    cN
    poimir.0
    nngt0d
    #
    @2
    @27
    @28
    @1
    cN
    cc0
    clt
    breq2
    biimparc
    sylan
    ad2ant2r
    poimirlem5
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
    @25
    poimirlem22.s
    wph
    @9
    @10
    @6
    simplrr
    #
    wph
    @5
    cc0
    @4
    clt
    wbr
    #
    @11
    @2
    wph
    @28
    @5
    @31
    @29
    @5
    @31
    @28
    @4
    cN
    cc0
    clt
    breq2
    biimparc
    sylan
    ad2ant2rl
    poimirlem5
    eqtr3d
    @13
    vn
    c1
    cN
    cfz
    co
    #
    @21
    @22
    @11
    @21
    @32
    wfn
    #
    wph
    @6
    @9
    @33
    @10
    @9
    @32
    @32
    @21
    wf1o
    #
    @33
    @9
    @21
    @32
    @32
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
    @34
    @9
    @0
    cc0
    cK
    cfzo
    co
    @32
    cmap
    co
    #
    @37
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
    @14
    @40
    wcel
    #
    @38
    @43
    @0
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
    clt
    wbr
    @47
    @47
    c1
    caddc
    co
    cif
    @48
    c1st
    cfv
    #
    c1st
    cfv
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
    cima
    c1
    csn
    cxp
    @50
    @51
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
    @42
    crab
    #
    cS
    @52
    vt
    @0
    @42
    elrabi
    poimirlem22.s
    eleq2s
    #
    @0
    @40
    @41
    xp1st
    #
    @14
    @39
    @37
    xp2nd
    3syl
    @36
    @34
    vf
    @21
    @14
    c2nd
    fvex
    @32
    @32
    @35
    @21
    f1oeq1
    elab
    sylib
    #
    @32
    @32
    @21
    f1ofn
    syl
    #
    adantr
    ad2antlr
    @11
    @22
    @32
    wfn
    #
    wph
    @6
    @10
    @58
    @9
    @10
    @32
    @32
    @22
    wf1o
    #
    @58
    @10
    @22
    @37
    wcel
    #
    @59
    @10
    @3
    @42
    wcel
    #
    @15
    @40
    wcel
    #
    @60
    @61
    @3
    @53
    cS
    @52
    vt
    @3
    @42
    elrabi
    poimirlem22.s
    eleq2s
    #
    @3
    @40
    @41
    xp1st
    #
    @15
    @39
    @37
    xp2nd
    3syl
    @36
    @59
    vf
    @22
    @15
    c2nd
    fvex
    @32
    @32
    @35
    @22
    f1oeq1
    elab
    sylib
    #
    @32
    @32
    @22
    f1ofn
    syl
    adantl
    ad2antlr
    @13
    vn
    cv
    #
    @32
    wcel
    #
    wa
    #
    @66
    @21
    cfv
    #
    csn
    #
    @66
    @22
    cfv
    #
    csn
    #
    wceq
    @69
    @71
    wceq
    @68
    @21
    c1
    @66
    cfz
    co
    #
    cima
    #
    @21
    c1
    @66
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
    @73
    cima
    #
    @22
    @76
    cima
    #
    cdif
    #
    @70
    @72
    @68
    @74
    @79
    @77
    @80
    @68
    @74
    @79
    wceq
    #
    @66
    cN
    @68
    @11
    @66
    cN
    wceq
    #
    @82
    wph
    @11
    @6
    @67
    simpllr
    @11
    @83
    wa
    @74
    @32
    @79
    @9
    @83
    @74
    @32
    wceq
    @10
    @83
    @9
    @74
    @21
    @32
    cima
    #
    @32
    @83
    @73
    @32
    @21
    @66
    cN
    c1
    cfz
    oveq2
    #
    imaeq2d
    @9
    @34
    @32
    @32
    @21
    wfo
    #
    @84
    @32
    wceq
    @56
    @32
    @32
    @21
    f1ofo
    @32
    @32
    @21
    foima
    3syl
    sylan9eqr
    adantlr
    @10
    @83
    @79
    @32
    wceq
    @9
    @83
    @10
    @79
    @22
    @32
    cima
    #
    @32
    @83
    @73
    @32
    @22
    @85
    imaeq2d
    @10
    @59
    @32
    @32
    @22
    wfo
    @87
    @32
    wceq
    @65
    @32
    @32
    @22
    f1ofo
    @32
    @32
    @22
    foima
    3syl
    sylan9eqr
    adantll
    eqtr4d
    sylan
    @13
    @67
    @66
    cN
    wne
    #
    @82
    @13
    @67
    @88
    wa
    #
    @66
    @46
    wcel
    #
    @82
    @13
    wph
    @89
    @90
    wph
    @11
    @6
    simpll
    #
    wph
    @89
    wa
    #
    @66
    c1
    @45
    cfz
    co
    #
    wcel
    #
    @83
    wn
    #
    wa
    #
    @90
    @92
    @94
    @83
    wo
    #
    @88
    wa
    #
    @96
    wph
    @89
    @98
    wph
    @67
    @97
    @88
    wph
    cN
    c1
    cuz
    cfv
    #
    wcel
    #
    @67
    @97
    wb
    wph
    @24
    @100
    poimir.0
    cN
    elnnuz
    sylib
    @66
    c1
    cN
    fzm1
    syl
    anbi1d
    biimpa
    @98
    @97
    @95
    wa
    @96
    @88
    @95
    @97
    @66
    cN
    df-ne
    anbi2i
    @94
    @83
    pm5.61
    bitri
    sylib
    @94
    @90
    @95
    @93
    @46
    @66
    c1
    cc0
    cuz
    cfv
    wcel
    @93
    @46
    wss
    1eluzge0
    c1
    cc0
    @45
    fzss1
    ax-mp
    sseli
    adantr
    syl
    sylan
    @13
    vm
    cv
    #
    @46
    wcel
    #
    wa
    #
    @21
    c1
    @101
    cfz
    co
    #
    cima
    #
    @22
    @104
    cima
    #
    wceq
    #
    wi
    #
    @13
    @90
    wa
    #
    @82
    wi
    vm
    vn
    vm
    vn
    weq
    #
    @103
    @109
    @107
    @82
    @110
    @102
    @90
    @13
    @101
    @66
    @46
    eleq1
    anbi2d
    @110
    @105
    @74
    @106
    @79
    @110
    @104
    @73
    @21
    @101
    @66
    c1
    cfz
    oveq2
    #
    imaeq2d
    @110
    @104
    @73
    @22
    @111
    imaeq2d
    eqeq12d
    imbi12d
    @103
    @105
    @106
    @103
    vy
    vt
    cS
    @0
    @3
    vf
    vj
    cF
    cK
    @101
    cN
    wph
    @24
    @11
    @6
    @102
    poimir.0
    ad3antrrr
    #
    poimirlem22.s
    wph
    @46
    cc0
    cK
    cfz
    co
    @32
    cmap
    co
    cF
    wf
    @11
    @6
    @102
    poimirlem22.1
    ad3antrrr
    #
    @11
    @9
    wph
    @6
    @102
    @9
    @10
    simpl
    ad3antlr
    #
    @12
    @2
    @5
    @102
    simplrl
    #
    @11
    @10
    wph
    @6
    @102
    @9
    @10
    simpr
    ad3antlr
    #
    @12
    @2
    @5
    @102
    simplrr
    #
    @13
    @102
    simpr
    #
    poimirlem12
    @103
    vy
    vt
    cS
    @3
    @0
    vf
    vj
    cF
    cK
    @101
    cN
    @112
    poimirlem22.s
    @113
    @116
    @117
    @114
    @115
    @118
    poimirlem12
    eqssd
    #
    chvarv
    syldan
    anassrs
    pm2.61dane
    @13
    @67
    @75
    @46
    wcel
    #
    @77
    @80
    wceq
    #
    @13
    wph
    @67
    @120
    @91
    wph
    @67
    wa
    @67
    @120
    wph
    @67
    simpr
    @67
    @66
    cz
    wcel
    #
    cN
    cz
    wcel
    @67
    @120
    wb
    wph
    @66
    c1
    cN
    elfzelz
    wph
    cN
    poimir.0
    nnzd
    @66
    cN
    elfzm1b
    syl2anr
    mpbid
    sylan
    @108
    @13
    @120
    wa
    #
    @121
    wi
    vm
    @75
    @66
    c1
    cmin
    ovex
    @101
    @75
    wceq
    #
    @103
    @123
    @107
    @121
    @124
    @102
    @120
    @13
    @101
    @75
    @46
    eleq1
    anbi2d
    @124
    @105
    @77
    @106
    @80
    @124
    @104
    @76
    @21
    @101
    @75
    c1
    cfz
    oveq2
    #
    imaeq2d
    @124
    @104
    @76
    @22
    @125
    imaeq2d
    eqeq12d
    imbi12d
    @119
    vtocl
    syldan
    difeq12d
    @13
    @9
    @67
    @70
    @78
    wceq
    #
    @26
    @9
    @67
    wa
    #
    @70
    @21
    @66
    csn
    #
    cima
    #
    @21
    @73
    @76
    cdif
    #
    cima
    #
    @78
    @9
    @33
    @67
    @70
    @129
    wceq
    @57
    @32
    @66
    @21
    fnsnfv
    sylan
    @67
    @131
    @129
    wceq
    @9
    @67
    @130
    @128
    @21
    @67
    @66
    cn
    wcel
    #
    @130
    @128
    wceq
    @66
    cN
    elfznn
    @132
    @76
    @128
    cun
    #
    @76
    cdif
    #
    @128
    @76
    cdif
    #
    @130
    @128
    @134
    @128
    @76
    cun
    #
    @76
    cdif
    @135
    @133
    @136
    @76
    @76
    @128
    uncom
    difeq1i
    @128
    @76
    difun2
    eqtri
    @132
    @73
    @133
    @76
    @132
    @73
    @76
    @75
    c1
    caddc
    co
    #
    @66
    cfz
    co
    #
    cun
    #
    @133
    @132
    @137
    @99
    wcel
    @66
    @75
    cuz
    cfv
    #
    wcel
    @73
    @139
    wceq
    @132
    @137
    @66
    @99
    @132
    @66
    cc
    wcel
    @137
    @66
    wceq
    @66
    nncn
    @66
    npcan1
    syl
    #
    @132
    @66
    @99
    wcel
    @66
    elnnuz
    biimpi
    eqeltrd
    @132
    @137
    @66
    @140
    @141
    @132
    @75
    cz
    wcel
    @75
    @140
    wcel
    @137
    @140
    wcel
    @132
    @75
    @66
    nnm1nn0
    nn0zd
    @75
    uzid
    @75
    @75
    peano2uz
    3syl
    eqeltrrd
    @75
    c1
    @66
    fzsplit2
    syl2anc
    @132
    @138
    @128
    @76
    @132
    @138
    @66
    @66
    cfz
    co
    #
    @128
    @132
    @137
    @66
    @66
    cfz
    @141
    oveq1d
    @132
    @122
    @142
    @128
    wceq
    @66
    nnz
    @66
    fzsn
    syl
    eqtrd
    uneq2d
    eqtrd
    difeq1d
    @132
    @66
    @76
    wcel
    #
    wn
    #
    @128
    @135
    wceq
    #
    @132
    @66
    cr
    wcel
    #
    @144
    @66
    nnre
    @146
    @66
    @75
    cle
    wbr
    #
    @143
    @146
    @75
    @66
    clt
    wbr
    #
    @147
    wn
    #
    @66
    ltm1
    @75
    cr
    wcel
    @146
    @148
    @149
    wb
    @66
    peano2rem
    @75
    @66
    ltnle
    mpancom
    mpbid
    @66
    c1
    @75
    elfzle2
    nsyl
    syl
    @76
    @128
    cin
    #
    c0
    wceq
    @128
    @76
    cin
    #
    c0
    wceq
    @144
    @145
    @150
    @151
    c0
    @76
    @128
    incom
    eqeq1i
    @76
    @66
    disjsn
    @128
    @76
    disj3
    3bitr3i
    sylib
    3eqtr4a
    syl
    imaeq2d
    adantl
    @9
    @131
    @78
    wceq
    #
    @67
    @9
    @34
    @21
    ccnv
    wfun
    #
    @152
    @56
    @34
    @86
    @153
    @32
    @32
    @21
    dff1o3
    simprbi
    @73
    @76
    @21
    imadif
    3syl
    adantr
    3eqtr2d
    #
    sylan
    @13
    @10
    @67
    @72
    @81
    wceq
    #
    @30
    @127
    @126
    wi
    @10
    @67
    wa
    #
    @155
    wi
    vz
    vk
    @7
    @127
    @156
    @126
    @155
    @7
    @9
    @10
    @67
    @0
    @3
    cS
    eleq1
    anbi1d
    @7
    @70
    @72
    @78
    @81
    @7
    @69
    @71
    @7
    @66
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
    @74
    @79
    @77
    @80
    @7
    @21
    @22
    @73
    @157
    imaeq1d
    @7
    @21
    @22
    @76
    @157
    imaeq1d
    difeq12d
    eqeq12d
    imbi12d
    @154
    chvarv
    sylan
    3eqtr4d
    @69
    @71
    @66
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
    @44
    @62
    @158
    @10
    @9
    @43
    @44
    @54
    @55
    syl
    @10
    @61
    @62
    @63
    @64
    syl
    @14
    @15
    @39
    @37
    @39
    @37
    xpopth
    syl2an
    ad2antlr
    mpbi2and
    @6
    @17
    @12
    @1
    @4
    cN
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
    @43
    @61
    @159
    @10
    @54
    @63
    @0
    @3
    @40
    @41
    @40
    @41
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
    cN
    @0
    @3
    c2nd
    fveq2
    eqeq1d
    rmo4
    sylibr
end
