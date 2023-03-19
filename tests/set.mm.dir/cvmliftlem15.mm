include "cv.mm"
include "c1.mm"
include "cmin.mm"
include "co.mm"
include "cdiv.mm"
include "cicc.mm"
include "wss.mm"
include "cima.mm"
include "cfv.mm"
include "wrex.mm"
include "cii.mm"
include "crab.mm"
include "cfz.mm"
include "wral.mm"
include "cn.mm"
include "ccom.mm"
include "wceq.mm"
include "cc0.mm"
include "wa.mm"
include "ccn.mm"
include "wreu.mm"
include "cuni.mm"
include "ssrab2.mm"
include "wcel.mm"
include "c0.mm"
include "wne.mm"
include "ccnv.mm"
include "ad2antrr.mm"
include "simprl.mm"
include "cnima.mm"
include "syl2anc.mm"
include "simplr.mm"
include "simprrl.mm"
include "wf.mm"
include "wfn.mm"
include "wb.mm"
include "iiuni.mm"
include "cnf.mm"
include "syl.mm"
include "ffn.mm"
include "elpreima.mm"
include "3syl.mm"
include "mpbir2and.mm"
include "simprrr.mm"
include "crn.mm"
include "cin.mm"
include "wfun.mm"
include "ffun.mm"
include "funimacnv.mm"
include "inss1.mm"
include "syl6eqss.mm"
include "ralrimivw.mm"
include "r19.2z.mm"
include "eleq2.mm"
include "imaeq2.mm"
include "sseq1d.mm"
include "rexbidv.mm"
include "anbi12d.mm"
include "rspcev.mm"
include "syl12anc.mm"
include "ccvm.mm"
include "adantr.mm"
include "ffvelrnda.mm"
include "cvmcov.mm"
include "reximddv.mm"
include "r19.42v.mm"
include "rexbii.mm"
include "rexcom.mm"
include "elunirab.mm"
include "3bitr4i.mm"
include "sylib.mm"
include "ex.mm"
include "ssrdv.mm"
include "uniss.mm"
include "mp1i.mm"
include "syl6sseqr.mm"
include "eqssd.mm"
include "lebnumii.mm"
include "sylancr.mm"
include "csn.mm"
include "cxp.mm"
include "ciun.mm"
include "c1st.mm"
include "wex.mm"
include "cfn.mm"
include "fzfi.mm"
include "weq.mm"
include "2rexbidv.mm"
include "rexrab.mm"
include "cop.mm"
include "vex.mm"
include "op1std.mm"
include "sseq2d.mm"
include "rexiunxp.mm"
include "wi.mm"
include "imass2.mm"
include "sstr2.mm"
include "reximdv.mm"
include "syl5bir.mm"
include "impcom.mm"
include "rexlimivw.mm"
include "sylbi.mm"
include "ralimi.mm"
include "fveq2.mm"
include "ac6sfi.mm"
include "cvv.mm"
include "c2nd.mm"
include "crio.mm"
include "cres.mm"
include "cmpt.mm"
include "cmpt2.mm"
include "cid.mm"
include "cun.mm"
include "cseq.mm"
include "cioo.mm"
include "ctg.mm"
include "sneq.mm"
include "xpeq12d.mm"
include "cbviunv.mm"
include "feq3.mm"
include "ax-mp.mm"
include "simprr.mm"
include "eqid.mm"
include "fveq2d.mm"
include "cbvmptv.mm"
include "cbvriotav.mm"
include "fveq1.mm"
include "eleq1d.mm"
include "riotabidv.mm"
include "syl5eq.mm"
include "reseq2d.mm"
include "cnveqd.mm"
include "fveq1d.mm"
include "mpteq2dv.mm"
include "oveq1.mm"
include "oveq1d.mm"
include "oveq12d.mm"
include "riotaeqbidv.mm"
include "mpteq12dv.mm"
include "cbvmpt2v.mm"
include "seqeq2.mm"
include "cvmliftlem14.mm"
include "exlimdv.mm"
include "syl5.mm"
include "rexlimdva.mm"
include "mpd.mm"

theorem cvmliftlem15
  let wph: wff ph
  let vv: setvar v
  let vu: setvar u
  let cB: class B
  let cC: class C
  let cP: class P
  let cS: class S
  let vf: setvar f
  let vk: setvar k
  let cF: class F
  let cG: class G
  let cJ: class J
  let cX: class X
  let vs: setvar s
  let vb: setvar b
  let vy: setvar y
  let vz: setvar z
  let va: setvar a
  let vc: setvar c
  let vg: setvar g
  let vj: setvar j
  let vm: setvar m
  let vn: setvar n
  let vt: setvar t
  let vw: setvar w
  let vx: setvar x
  let cL: class L
  let cK: class K
  let cM: class M
  let wps: wff ps
  let cN: class N
  let cT: class T
  let cQ: class Q
  let cW: class W
  assume cvmliftlem.1: |- S = ( k e. J |-> { s e. ( ~P C \ { (/) } ) | ( U. s = ( `' F " k ) /\ A. u e. s ( A. v e. ( s \ { u } ) ( u i^i v ) = (/) /\ ( F |` u ) e. ( ( C |`t u ) Homeo ( J |`t k ) ) ) ) } )
  assume cvmliftlem.b: |- B = U. C
  assume cvmliftlem.x: |- X = U. J
  assume cvmliftlem.f: |- ( ph -> F e. ( C CovMap J ) )
  assume cvmliftlem.g: |- ( ph -> G e. ( II Cn J ) )
  assume cvmliftlem.p: |- ( ph -> P e. B )
  assume cvmliftlem.e: |- ( ph -> ( F ` P ) = ( G ` 0 ) )

  disjoint B v
  disjoint f k
  disjoint f s
  disjoint f u
  disjoint f v
  disjoint F f
  disjoint k s
  disjoint k u
  disjoint k v
  disjoint F k
  disjoint s u
  disjoint s v
  disjoint F s
  disjoint u v
  disjoint F u
  disjoint F v
  disjoint P f
  disjoint P k
  disjoint P u
  disjoint P v
  disjoint C f
  disjoint C k
  disjoint C s
  disjoint C u
  disjoint C v
  disjoint f ph
  disjoint ph s
  disjoint S f
  disjoint S k
  disjoint S s
  disjoint S u
  disjoint S v
  disjoint G f
  disjoint G k
  disjoint G s
  disjoint G u
  disjoint G v
  disjoint J f
  disjoint J k
  disjoint J s
  disjoint J u
  disjoint J v
  disjoint b v
  disjoint b y
  disjoint b z
  disjoint B b
  disjoint v y
  disjoint v z
  disjoint y z
  disjoint B y
  disjoint B z
  disjoint a b
  disjoint a c
  disjoint a f
  disjoint a g
  disjoint a j
  disjoint a k
  disjoint a m
  disjoint a n
  disjoint a s
  disjoint a t
  disjoint a u
  disjoint a v
  disjoint a w
  disjoint a x
  disjoint a y
  disjoint a z
  disjoint F a
  disjoint b c
  disjoint b f
  disjoint b g
  disjoint b j
  disjoint b k
  disjoint b m
  disjoint b n
  disjoint b s
  disjoint b t
  disjoint b u
  disjoint b w
  disjoint b x
  disjoint F b
  disjoint c f
  disjoint c g
  disjoint c j
  disjoint c k
  disjoint c m
  disjoint c n
  disjoint c s
  disjoint c t
  disjoint c u
  disjoint c v
  disjoint c w
  disjoint c x
  disjoint c y
  disjoint c z
  disjoint F c
  disjoint f g
  disjoint f j
  disjoint f m
  disjoint f n
  disjoint f t
  disjoint f w
  disjoint f x
  disjoint f y
  disjoint f z
  disjoint g j
  disjoint g k
  disjoint g m
  disjoint g n
  disjoint g s
  disjoint g t
  disjoint g u
  disjoint g v
  disjoint g w
  disjoint g x
  disjoint g y
  disjoint g z
  disjoint F g
  disjoint j k
  disjoint j m
  disjoint j n
  disjoint j s
  disjoint j t
  disjoint j u
  disjoint j v
  disjoint j w
  disjoint j x
  disjoint j y
  disjoint j z
  disjoint F j
  disjoint k m
  disjoint k n
  disjoint k t
  disjoint k w
  disjoint k x
  disjoint k y
  disjoint k z
  disjoint m n
  disjoint m s
  disjoint m t
  disjoint m u
  disjoint m v
  disjoint m w
  disjoint m x
  disjoint m y
  disjoint m z
  disjoint F m
  disjoint n s
  disjoint n t
  disjoint n u
  disjoint n v
  disjoint n w
  disjoint n x
  disjoint n y
  disjoint n z
  disjoint F n
  disjoint s t
  disjoint s w
  disjoint s x
  disjoint s y
  disjoint s z
  disjoint t u
  disjoint t v
  disjoint t w
  disjoint t x
  disjoint t y
  disjoint t z
  disjoint F t
  disjoint u w
  disjoint u x
  disjoint u y
  disjoint u z
  disjoint v w
  disjoint v x
  disjoint w x
  disjoint w y
  disjoint w z
  disjoint F w
  disjoint x y
  disjoint x z
  disjoint F x
  disjoint F y
  disjoint F z
  disjoint L n
  disjoint L y
  disjoint L z
  disjoint K f
  disjoint K y
  disjoint M a
  disjoint M b
  disjoint M c
  disjoint M j
  disjoint M k
  disjoint M m
  disjoint M s
  disjoint M u
  disjoint M v
  disjoint M x
  disjoint M y
  disjoint M z
  disjoint P b
  disjoint P g
  disjoint P m
  disjoint P n
  disjoint P x
  disjoint P z
  disjoint C a
  disjoint C b
  disjoint C c
  disjoint C g
  disjoint C j
  disjoint C n
  disjoint C y
  disjoint C z
  disjoint a ph
  disjoint g ph
  disjoint j ph
  disjoint n ph
  disjoint ph x
  disjoint ph y
  disjoint ph z
  disjoint ps z
  disjoint N b
  disjoint N c
  disjoint N k
  disjoint N m
  disjoint N n
  disjoint N u
  disjoint N v
  disjoint N x
  disjoint N y
  disjoint N z
  disjoint S a
  disjoint S b
  disjoint S g
  disjoint S j
  disjoint S n
  disjoint S x
  disjoint S z
  disjoint X a
  disjoint X j
  disjoint G a
  disjoint G b
  disjoint G g
  disjoint G j
  disjoint G m
  disjoint G n
  disjoint G t
  disjoint G w
  disjoint G x
  disjoint G y
  disjoint G z
  disjoint T a
  disjoint T b
  disjoint T c
  disjoint T j
  disjoint T k
  disjoint T m
  disjoint T s
  disjoint T u
  disjoint T v
  disjoint T x
  disjoint T y
  disjoint T z
  disjoint J a
  disjoint J b
  disjoint J c
  disjoint J g
  disjoint J j
  disjoint J n
  disjoint J x
  disjoint J z
  disjoint Q b
  disjoint Q c
  disjoint Q k
  disjoint Q m
  disjoint Q n
  disjoint Q u
  disjoint Q v
  disjoint Q x
  disjoint Q y
  disjoint Q z
  disjoint W k
  disjoint W m
  disjoint W x
  disjoint W z
  assert |- ( ph -> E! f e. ( II Cn C ) ( ( F o. f ) = G /\ ( f ` 0 ) = P ) )

  proof
    wph
    vk
    cv
    #
    c1
    cmin
    co
    vn
    cv
    #
    cdiv
    co
    @0
    @1
    cdiv
    co
    cicc
    co
    #
    vv
    cv
    #
    wss
    #
    vv
    cG
    vu
    cv
    #
    cima
    #
    vj
    cv
    #
    wss
    #
    vs
    @7
    cS
    cfv
    #
    wrex
    #
    vj
    cJ
    wrex
    #
    vu
    cii
    crab
    #
    wrex
    #
    vk
    c1
    @1
    cfz
    co
    #
    wral
    #
    vn
    cn
    wrex
    #
    cF
    vf
    cv
    #
    ccom
    cG
    wceq
    cc0
    @17
    cfv
    cP
    wceq
    wa
    vf
    cii
    cC
    ccn
    co
    wreu
    #
    wph
    @12
    cii
    wss
    #
    cc0
    c1
    cicc
    co
    #
    @12
    cuni
    #
    wceq
    @16
    @11
    vu
    cii
    ssrab2
    #
    wph
    @20
    @21
    wph
    vx
    @20
    @21
    wph
    vx
    cv
    #
    @20
    wcel
    #
    @23
    @21
    wcel
    #
    wph
    @24
    wa
    #
    @23
    @5
    wcel
    #
    @10
    wa
    #
    vu
    cii
    wrex
    #
    vj
    cJ
    wrex
    #
    @25
    @26
    @23
    cG
    cfv
    #
    @7
    wcel
    #
    @9
    c0
    wne
    #
    wa
    #
    @29
    vj
    cJ
    @26
    @7
    cJ
    wcel
    #
    @34
    wa
    #
    wa
    #
    cG
    ccnv
    @7
    cima
    #
    cii
    wcel
    #
    @23
    @38
    wcel
    #
    cG
    @38
    cima
    #
    @7
    wss
    #
    vs
    @9
    wrex
    #
    @29
    @37
    cG
    cii
    cJ
    ccn
    co
    wcel
    #
    @35
    @39
    wph
    @44
    @24
    @36
    cvmliftlem.g
    ad2antrr
    @26
    @35
    @34
    simprl
    @7
    cG
    cii
    cJ
    cnima
    syl2anc
    @37
    @40
    @24
    @32
    wph
    @24
    @36
    simplr
    @26
    @35
    @32
    @33
    simprrl
    @37
    @20
    cX
    cG
    wf
    #
    cG
    @20
    wfn
    @40
    @24
    @32
    wa
    wb
    wph
    @45
    @24
    @36
    wph
    @44
    @45
    cvmliftlem.g
    cG
    cii
    cJ
    @20
    cX
    iiuni
    cvmliftlem.x
    cnf
    syl
    #
    ad2antrr
    #
    @20
    cX
    cG
    ffn
    @20
    @23
    @7
    cG
    elpreima
    3syl
    mpbir2and
    @37
    @33
    @42
    vs
    @9
    wral
    @43
    @26
    @35
    @32
    @33
    simprrr
    @37
    @42
    vs
    @9
    @37
    @41
    @7
    cG
    crn
    #
    cin
    #
    @7
    @37
    @45
    cG
    wfun
    @41
    @49
    wceq
    @47
    @20
    cX
    cG
    ffun
    @7
    cG
    funimacnv
    3syl
    @7
    @48
    inss1
    syl6eqss
    ralrimivw
    @42
    vs
    @9
    r19.2z
    syl2anc
    @28
    @40
    @43
    wa
    vu
    @38
    cii
    @5
    @38
    wceq
    #
    @27
    @40
    @10
    @43
    @5
    @38
    @23
    eleq2
    @50
    @8
    @42
    vs
    @9
    @50
    @6
    @41
    @7
    @5
    @38
    cG
    imaeq2
    sseq1d
    rexbidv
    anbi12d
    rspcev
    syl12anc
    @26
    cF
    cC
    cJ
    ccvm
    co
    wcel
    #
    @31
    cX
    wcel
    @34
    vj
    cJ
    wrex
    wph
    @51
    @24
    cvmliftlem.f
    adantr
    wph
    @20
    cX
    @23
    cG
    @46
    ffvelrnda
    vj
    vv
    vu
    cC
    @31
    cS
    vk
    cF
    cJ
    cX
    vs
    cvmliftlem.1
    cvmliftlem.x
    cvmcov
    syl2anc
    reximddv
    @28
    vj
    cJ
    wrex
    #
    vu
    cii
    wrex
    @27
    @11
    wa
    #
    vu
    cii
    wrex
    @30
    @25
    @52
    @53
    vu
    cii
    @27
    @10
    vj
    cJ
    r19.42v
    rexbii
    @28
    vj
    vu
    cJ
    cii
    rexcom
    @11
    vu
    @23
    cii
    elunirab
    3bitr4i
    sylib
    ex
    ssrdv
    wph
    @21
    cii
    cuni
    #
    @20
    @19
    @21
    @54
    wss
    wph
    @22
    @12
    cii
    uniss
    mp1i
    iiuni
    syl6sseqr
    eqssd
    vv
    @12
    vk
    vn
    lebnumii
    sylancr
    wph
    @15
    @18
    vn
    cn
    @15
    @14
    vj
    cJ
    @7
    csn
    #
    @9
    cxp
    #
    ciun
    #
    vg
    cv
    #
    wf
    #
    cG
    @2
    cima
    #
    @0
    @58
    cfv
    #
    c1st
    cfv
    #
    wss
    #
    vk
    @14
    wral
    #
    wa
    #
    vg
    wex
    #
    wph
    @1
    cn
    wcel
    #
    wa
    #
    @18
    @15
    @14
    cfn
    wcel
    @60
    @5
    c1st
    cfv
    #
    wss
    #
    vu
    @57
    wrex
    #
    vk
    @14
    wral
    @66
    c1
    @1
    fzfi
    @13
    @71
    vk
    @14
    @13
    cG
    @3
    cima
    #
    @7
    wss
    #
    vs
    @9
    wrex
    vj
    cJ
    wrex
    #
    @4
    wa
    #
    vv
    cii
    wrex
    @71
    @11
    @74
    @4
    vv
    vu
    cii
    vu
    vv
    weq
    #
    @8
    @73
    vj
    vs
    cJ
    @9
    @76
    @6
    @72
    @7
    @5
    @3
    cG
    imaeq2
    sseq1d
    2rexbidv
    rexrab
    @75
    @71
    vv
    cii
    @4
    @74
    @71
    @74
    @72
    @69
    wss
    #
    vu
    @57
    wrex
    @4
    @71
    @77
    @73
    vu
    vj
    vs
    cJ
    @9
    @5
    @7
    vs
    cv
    #
    cop
    wceq
    @69
    @7
    @72
    @7
    @78
    @5
    vj
    vex
    vs
    vex
    op1std
    sseq2d
    rexiunxp
    @4
    @77
    @70
    vu
    @57
    @4
    @60
    @72
    wss
    @77
    @70
    wi
    @2
    @3
    cG
    imass2
    @60
    @72
    @69
    sstr2
    syl
    reximdv
    syl5bir
    impcom
    rexlimivw
    sylbi
    ralimi
    @70
    @63
    vk
    vu
    @14
    @57
    vg
    @5
    @61
    wceq
    @69
    @62
    @60
    @5
    @61
    c1st
    fveq2
    sseq2d
    ac6sfi
    sylancr
    @68
    @65
    @18
    vg
    @68
    @65
    @18
    @68
    @65
    wa
    #
    vx
    vz
    vv
    vu
    cB
    cC
    cP
    vy
    vw
    cvv
    cn
    vt
    vw
    cv
    #
    c1
    cmin
    co
    #
    @1
    cdiv
    co
    #
    @80
    @1
    cdiv
    co
    #
    cicc
    co
    #
    vt
    cv
    #
    cG
    cfv
    #
    cF
    @82
    vy
    cv
    #
    cfv
    #
    vc
    cv
    #
    wcel
    #
    vc
    @80
    @58
    cfv
    #
    c2nd
    cfv
    #
    crio
    #
    cres
    #
    ccnv
    #
    cfv
    #
    cmpt
    #
    cmpt2
    #
    cid
    cn
    cres
    cc0
    cc0
    cP
    cop
    csn
    cop
    csn
    cun
    #
    cc0
    cseq
    #
    cS
    @58
    vf
    va
    vk
    vm
    cF
    cG
    cJ
    vk
    @14
    @0
    @100
    cfv
    ciun
    #
    cioo
    crn
    ctg
    cfv
    #
    @1
    cX
    vs
    vb
    cvmliftlem.1
    cvmliftlem.b
    cvmliftlem.x
    wph
    @51
    @67
    @65
    cvmliftlem.f
    ad2antrr
    wph
    @44
    @67
    @65
    cvmliftlem.g
    ad2antrr
    wph
    cP
    cB
    wcel
    @67
    @65
    cvmliftlem.p
    ad2antrr
    wph
    cP
    cF
    cfv
    cc0
    cG
    cfv
    wceq
    @67
    @65
    cvmliftlem.e
    ad2antrr
    wph
    @67
    @65
    simplr
    @79
    @59
    @14
    va
    cJ
    va
    cv
    #
    csn
    #
    @103
    cS
    cfv
    #
    cxp
    #
    ciun
    #
    @58
    wf
    #
    @68
    @59
    @64
    simprl
    @57
    @107
    wceq
    @59
    @108
    wb
    vj
    va
    cJ
    @56
    @106
    vj
    va
    weq
    @55
    @104
    @9
    @105
    @7
    @103
    sneq
    @7
    @103
    cS
    fveq2
    xpeq12d
    cbviunv
    @57
    @107
    @14
    @58
    feq3
    ax-mp
    sylib
    @68
    @59
    @64
    simprr
    @102
    eqid
    @98
    vx
    vm
    cvv
    cn
    vz
    vm
    cv
    #
    c1
    cmin
    co
    #
    @1
    cdiv
    co
    #
    @109
    @1
    cdiv
    co
    #
    cicc
    co
    #
    vz
    cv
    #
    cG
    cfv
    #
    cF
    @111
    @23
    cfv
    #
    vb
    cv
    #
    wcel
    #
    vb
    @109
    @58
    cfv
    #
    c2nd
    cfv
    #
    crio
    #
    cres
    #
    ccnv
    #
    cfv
    #
    cmpt
    #
    cmpt2
    #
    wceq
    @100
    @126
    @99
    cc0
    cseq
    wceq
    vy
    vw
    vx
    vm
    cvv
    cn
    @97
    @125
    vz
    @84
    @115
    cF
    @82
    @23
    cfv
    #
    @117
    wcel
    #
    vb
    @92
    crio
    #
    cres
    #
    ccnv
    #
    cfv
    #
    cmpt
    #
    vy
    vx
    weq
    #
    @97
    vz
    @84
    @115
    @95
    cfv
    #
    cmpt
    @133
    vt
    vz
    @84
    @96
    @135
    vt
    vz
    weq
    @86
    @115
    @95
    @85
    @114
    cG
    fveq2
    fveq2d
    cbvmptv
    @134
    vz
    @84
    @135
    @132
    @134
    @115
    @95
    @131
    @134
    @94
    @130
    @134
    @93
    @129
    cF
    @134
    @93
    @88
    @117
    wcel
    #
    vb
    @92
    crio
    @129
    @90
    @136
    vc
    vb
    @92
    @89
    @117
    @88
    eleq2
    cbvriotav
    @134
    @136
    @128
    vb
    @92
    @134
    @88
    @127
    @117
    @82
    @87
    @23
    fveq1
    eleq1d
    riotabidv
    syl5eq
    reseq2d
    cnveqd
    fveq1d
    mpteq2dv
    syl5eq
    vw
    vm
    weq
    #
    vz
    @84
    @132
    @113
    @124
    @137
    @82
    @111
    @83
    @112
    cicc
    @137
    @81
    @110
    @1
    cdiv
    @80
    @109
    c1
    cmin
    oveq1
    oveq1d
    #
    @80
    @109
    @1
    cdiv
    oveq1
    oveq12d
    @137
    @115
    @131
    @123
    @137
    @130
    @122
    @137
    @129
    @121
    cF
    @137
    @128
    @118
    vb
    @92
    @120
    @137
    @91
    @119
    c2nd
    @80
    @109
    @58
    fveq2
    fveq2d
    @137
    @127
    @116
    @117
    @137
    @82
    @111
    @23
    @138
    fveq2d
    eleq1d
    riotaeqbidv
    reseq2d
    cnveqd
    fveq1d
    mpteq12dv
    cbvmpt2v
    @98
    @126
    @99
    cc0
    seqeq2
    ax-mp
    @101
    eqid
    cvmliftlem14
    ex
    exlimdv
    syl5
    rexlimdva
    mpd
end
