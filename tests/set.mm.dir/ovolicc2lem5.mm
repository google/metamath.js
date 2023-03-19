include "cv.mm"
include "wcel.mm"
include "cmin.mm"
include "co.mm"
include "crn.mm"
include "cxr.mm"
include "clt.mm"
include "csup.mm"
include "cle.mm"
include "wbr.mm"
include "cuni.mm"
include "wrex.mm"
include "cicc.mm"
include "rexrd.mm"
include "lbicc2.mm"
include "syl3anc.mm"
include "sseldd.mm"
include "eluni2.mm"
include "sylib.mm"
include "wa.mm"
include "wf.mm"
include "cfv.mm"
include "c2nd.mm"
include "cif.mm"
include "wral.mm"
include "wex.mm"
include "cfn.mm"
include "wss.mm"
include "cioo.mm"
include "ccom.mm"
include "cpw.mm"
include "cin.mm"
include "elin.mm"
include "simprd.mm"
include "c0.mm"
include "wne.mm"
include "crab.mm"
include "ssrab2.mm"
include "eqsstri.mm"
include "ssfi.mm"
include "sylancl.mm"
include "adantr.mm"
include "cr.mm"
include "cxp.mm"
include "inss2.mm"
include "cn.mm"
include "wceq.mm"
include "ineq1.mm"
include "neeq1d.mm"
include "elrab2.mm"
include "simplbi.mm"
include "ffvelrn.mm"
include "syl2an.mm"
include "ffvelrnda.mm"
include "syldan.mm"
include "sseldi.mm"
include "xp2nd.mm"
include "syl.mm"
include "ifcld.mm"
include "simprbi.mm"
include "adantl.mm"
include "n0.mm"
include "w3a.mm"
include "simprr.mm"
include "wb.mm"
include "elicc2.mm"
include "syl2anc.mm"
include "mpbid.mm"
include "simp1d.mm"
include "adantrr.mm"
include "simp2d.mm"
include "c1st.mm"
include "simpld.mm"
include "fvco3.mm"
include "sylan.mm"
include "sylan2.mm"
include "cop.mm"
include "1st2nd2.mm"
include "fveq2d.mm"
include "df-ov.mm"
include "syl6eqr.mm"
include "3eqtr3d.mm"
include "eleqtrd.mm"
include "xp1st.mm"
include "rexr.mm"
include "elioo2.mm"
include "simp3d.mm"
include "ltled.mm"
include "letrd.mm"
include "expr.mm"
include "exlimdv.mm"
include "mpd.mm"
include "breq2.mm"
include "ifboth.mm"
include "min2.mm"
include "mpbir3and.mm"
include "simprl.mm"
include "inelcm.mm"
include "sylanbrc.mm"
include "jca.mm"
include "ex.mm"
include "reximdv2.mm"
include "ralrimiva.mm"
include "eleq2.mm"
include "ac6sfi.mm"
include "fveq2.mm"
include "breq1d.mm"
include "ifbieq1d.mm"
include "eleq12d.mm"
include "cbvralv.mm"
include "csn.mm"
include "c1.mm"
include "cseq.mm"
include "cinf.mm"
include "adantlr.mm"
include "simprrl.mm"
include "simprrr.mm"
include "rspccva.mm"
include "simprlr.mm"
include "simprll.mm"
include "eqid.mm"
include "eleq2d.mm"
include "cbvrabv.mm"
include "ovolicc2lem4.mm"
include "anassrs.mm"
include "syl5bir.mm"
include "expimpd.mm"
include "rexlimddv.mm"

theorem ovolicc2lem5
  let wph: wff ph
  let vu: setvar u
  let vt: setvar t
  let cA: class A
  let cB: class B
  let cS: class S
  let cT: class T
  let cU: class U
  let cF: class F
  let cG: class G
  let vf: setvar f
  let vg: setvar g
  let vh: setvar h
  let vk: setvar k
  let vm: setvar m
  let vn: setvar n
  let vv: setvar v
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cH: class H
  let cC: class C
  let vi: setvar i
  let vj: setvar j
  let cK: class K
  let cM: class M
  let cW: class W
  let cP: class P
  let cN: class N
  let cX: class X
  assume ovolicc.1: |- ( ph -> A e. RR )
  assume ovolicc.2: |- ( ph -> B e. RR )
  assume ovolicc.3: |- ( ph -> A <_ B )
  assume ovolicc2.4: |- S = seq 1 ( + , ( ( abs o. - ) o. F ) )
  assume ovolicc2.5: |- ( ph -> F : NN --> ( <_ i^i ( RR X. RR ) ) )
  assume ovolicc2.6: |- ( ph -> U e. ( ~P ran ( (,) o. F ) i^i Fin ) )
  assume ovolicc2.7: |- ( ph -> ( A [,] B ) C_ U. U )
  assume ovolicc2.8: |- ( ph -> G : U --> NN )
  assume ovolicc2.9: |- ( ( ph /\ t e. U ) -> ( ( (,) o. F ) ` ( G ` t ) ) = t )
  assume ovolicc2.10: |- T = { u e. U | ( u i^i ( A [,] B ) ) =/= (/) }

  disjoint t u
  disjoint A t
  disjoint A u
  disjoint B t
  disjoint B u
  disjoint F t
  disjoint G t
  disjoint ph t
  disjoint T t
  disjoint U t
  disjoint U u
  disjoint f g
  disjoint f h
  disjoint f k
  disjoint f m
  disjoint f n
  disjoint f t
  disjoint f u
  disjoint f v
  disjoint f x
  disjoint f y
  disjoint f z
  disjoint A f
  disjoint g h
  disjoint g k
  disjoint g m
  disjoint g n
  disjoint g t
  disjoint g u
  disjoint g v
  disjoint g x
  disjoint g y
  disjoint g z
  disjoint A g
  disjoint h k
  disjoint h m
  disjoint h n
  disjoint h t
  disjoint h u
  disjoint h v
  disjoint h x
  disjoint h y
  disjoint h z
  disjoint A h
  disjoint k m
  disjoint k n
  disjoint k t
  disjoint k u
  disjoint k v
  disjoint k x
  disjoint k y
  disjoint k z
  disjoint A k
  disjoint m n
  disjoint m t
  disjoint m u
  disjoint m v
  disjoint m x
  disjoint m y
  disjoint m z
  disjoint A m
  disjoint n t
  disjoint n u
  disjoint n v
  disjoint n x
  disjoint n y
  disjoint n z
  disjoint A n
  disjoint t v
  disjoint t x
  disjoint t y
  disjoint t z
  disjoint u v
  disjoint u x
  disjoint u y
  disjoint u z
  disjoint v x
  disjoint v y
  disjoint v z
  disjoint A v
  disjoint x y
  disjoint x z
  disjoint A x
  disjoint y z
  disjoint A y
  disjoint A z
  disjoint B f
  disjoint B g
  disjoint B h
  disjoint B k
  disjoint B m
  disjoint B n
  disjoint B v
  disjoint B x
  disjoint B y
  disjoint B z
  disjoint H t
  disjoint C f
  disjoint C g
  disjoint C k
  disjoint C m
  disjoint C n
  disjoint C t
  disjoint C y
  disjoint C z
  disjoint h i
  disjoint h j
  disjoint F h
  disjoint i j
  disjoint i k
  disjoint i n
  disjoint i t
  disjoint i x
  disjoint i y
  disjoint F i
  disjoint j k
  disjoint j n
  disjoint j t
  disjoint j x
  disjoint j y
  disjoint F j
  disjoint F k
  disjoint F n
  disjoint F x
  disjoint F y
  disjoint i u
  disjoint i z
  disjoint K i
  disjoint j u
  disjoint j z
  disjoint K j
  disjoint K k
  disjoint K n
  disjoint K t
  disjoint K u
  disjoint K x
  disjoint K y
  disjoint K z
  disjoint f i
  disjoint f j
  disjoint G f
  disjoint G h
  disjoint G i
  disjoint G j
  disjoint G k
  disjoint G n
  disjoint G x
  disjoint G y
  disjoint G z
  disjoint i m
  disjoint M i
  disjoint j m
  disjoint M j
  disjoint M m
  disjoint M n
  disjoint M t
  disjoint M x
  disjoint M y
  disjoint M z
  disjoint W i
  disjoint W j
  disjoint W k
  disjoint W m
  disjoint W n
  disjoint W x
  disjoint W y
  disjoint P k
  disjoint P y
  disjoint f ph
  disjoint g i
  disjoint g j
  disjoint g ph
  disjoint h ph
  disjoint i v
  disjoint i ph
  disjoint j v
  disjoint j ph
  disjoint k ph
  disjoint m ph
  disjoint n ph
  disjoint ph v
  disjoint ph x
  disjoint ph y
  disjoint ph z
  disjoint T f
  disjoint T h
  disjoint T k
  disjoint T n
  disjoint T x
  disjoint T y
  disjoint T z
  disjoint N k
  disjoint N n
  disjoint N t
  disjoint N u
  disjoint N x
  disjoint N y
  disjoint S h
  disjoint S z
  disjoint U h
  disjoint U n
  disjoint U x
  disjoint U z
  disjoint X t
  assert |- ( ph -> ( B - A ) <_ sup ( ran S , RR* , < ) )

  proof
    wph
    cA
    vz
    cv
    #
    wcel
    #
    cB
    cA
    cmin
    co
    cS
    crn
    cxr
    clt
    csup
    cle
    wbr
    #
    vz
    cU
    wph
    cA
    cU
    cuni
    #
    wcel
    @1
    vz
    cU
    wrex
    wph
    cA
    cB
    cicc
    co
    #
    @3
    cA
    ovolicc2.7
    wph
    cA
    cxr
    wcel
    cB
    cxr
    wcel
    cA
    cB
    cle
    wbr
    #
    cA
    @4
    wcel
    #
    wph
    cA
    ovolicc.1
    rexrd
    wph
    cB
    ovolicc.2
    rexrd
    ovolicc.3
    cA
    cB
    lbicc2
    syl3anc
    #
    sseldd
    vz
    cA
    cU
    eluni2
    sylib
    wph
    @0
    cU
    wcel
    #
    @1
    wa
    #
    wa
    #
    cT
    cT
    vh
    cv
    #
    wf
    #
    vt
    cv
    #
    cG
    cfv
    #
    cF
    cfv
    #
    c2nd
    cfv
    #
    cB
    cle
    wbr
    #
    @16
    cB
    cif
    #
    @13
    @11
    cfv
    #
    wcel
    #
    vt
    cT
    wral
    #
    wa
    #
    vh
    wex
    #
    @2
    wph
    @23
    @9
    wph
    cT
    cfn
    wcel
    #
    @18
    vx
    cv
    #
    wcel
    #
    vx
    cT
    wrex
    #
    vt
    cT
    wral
    @23
    wph
    cU
    cfn
    wcel
    #
    cT
    cU
    wss
    @24
    wph
    cU
    cioo
    cF
    ccom
    #
    crn
    cpw
    #
    wcel
    #
    @28
    wph
    cU
    @30
    cfn
    cin
    wcel
    #
    @31
    @28
    wa
    ovolicc2.6
    cU
    @30
    cfn
    elin
    sylib
    simprd
    cT
    vu
    cv
    #
    @4
    cin
    #
    c0
    wne
    #
    vu
    cU
    crab
    cU
    ovolicc2.10
    @35
    vu
    cU
    ssrab2
    eqsstri
    cU
    cT
    ssfi
    sylancl
    wph
    @27
    vt
    cT
    wph
    @13
    cT
    wcel
    #
    wa
    #
    @26
    vx
    cU
    wrex
    #
    @27
    @37
    @18
    @3
    wcel
    @38
    @37
    @4
    @3
    @18
    wph
    @4
    @3
    wss
    #
    @36
    ovolicc2.7
    adantr
    @37
    @18
    @4
    wcel
    #
    @18
    cr
    wcel
    #
    cA
    @18
    cle
    wbr
    #
    @18
    cB
    cle
    wbr
    #
    @37
    @17
    @16
    cB
    cr
    @37
    @15
    cr
    cr
    cxp
    #
    wcel
    #
    @16
    cr
    wcel
    #
    @37
    cle
    @44
    cin
    #
    @44
    @15
    cle
    @44
    inss2
    wph
    @36
    @14
    cn
    wcel
    #
    @15
    @47
    wcel
    wph
    cU
    cn
    cG
    wf
    #
    @13
    cU
    wcel
    #
    @48
    @36
    ovolicc2.8
    @36
    @50
    @13
    @4
    cin
    #
    c0
    wne
    #
    @35
    @52
    vu
    @13
    cU
    cT
    @33
    @13
    wceq
    @34
    @51
    c0
    @33
    @13
    @4
    ineq1
    neeq1d
    ovolicc2.10
    elrab2
    #
    simplbi
    #
    cU
    cn
    @13
    cG
    ffvelrn
    syl2an
    #
    wph
    cn
    @47
    @14
    cF
    ovolicc2.5
    ffvelrnda
    syldan
    sseldi
    #
    @15
    cr
    cr
    xp2nd
    #
    syl
    #
    wph
    cB
    cr
    wcel
    #
    @36
    ovolicc.2
    adantr
    #
    ifcld
    @37
    cA
    @16
    cle
    wbr
    #
    @5
    @42
    @37
    vy
    cv
    #
    @51
    wcel
    #
    vy
    wex
    #
    @61
    @37
    @52
    @64
    @36
    @52
    wph
    @36
    @50
    @52
    @53
    simprbi
    adantl
    vy
    @51
    n0
    sylib
    @37
    @63
    @61
    vy
    wph
    @36
    @63
    @61
    wph
    @36
    @63
    wa
    #
    wa
    #
    cA
    @62
    @16
    wph
    cA
    cr
    wcel
    #
    @65
    ovolicc.1
    adantr
    #
    @66
    @62
    cr
    wcel
    #
    cA
    @62
    cle
    wbr
    #
    @62
    cB
    cle
    wbr
    #
    @66
    @62
    @4
    wcel
    #
    @69
    @70
    @71
    w3a
    #
    @66
    @62
    @13
    wcel
    #
    @72
    @66
    @63
    @74
    @72
    wa
    wph
    @36
    @63
    simprr
    @62
    @13
    @4
    elin
    sylib
    #
    simprd
    @66
    @67
    @59
    @72
    @73
    wb
    @68
    wph
    @59
    @65
    ovolicc.2
    adantr
    cA
    cB
    @62
    elicc2
    syl2anc
    mpbid
    #
    simp1d
    #
    @66
    @45
    @46
    wph
    @36
    @45
    @63
    @56
    adantrr
    #
    @57
    syl
    #
    @66
    @69
    @70
    @71
    @76
    simp2d
    @66
    @62
    @16
    @77
    @79
    @66
    @69
    @15
    c1st
    cfv
    #
    @62
    clt
    wbr
    #
    @62
    @16
    clt
    wbr
    #
    @66
    @62
    @80
    @16
    cioo
    co
    #
    wcel
    #
    @69
    @81
    @82
    w3a
    #
    @66
    @62
    @13
    @83
    @66
    @74
    @72
    @75
    simpld
    @66
    @14
    @29
    cfv
    #
    @15
    cioo
    cfv
    #
    @13
    @83
    wph
    @65
    @48
    @86
    @87
    wceq
    #
    wph
    @36
    @48
    @63
    @55
    adantrr
    wph
    cn
    @47
    cF
    wf
    #
    @48
    @88
    ovolicc2.5
    cn
    @47
    @14
    cioo
    cF
    fvco3
    sylan
    syldan
    wph
    @36
    @86
    @13
    wceq
    #
    @63
    @36
    wph
    @50
    @90
    @54
    ovolicc2.9
    sylan2
    adantrr
    @66
    @87
    @80
    @16
    cop
    #
    cioo
    cfv
    @83
    @66
    @15
    @91
    cioo
    @66
    @45
    @15
    @91
    wceq
    @78
    @15
    cr
    cr
    1st2nd2
    syl
    fveq2d
    @80
    @16
    cioo
    df-ov
    syl6eqr
    3eqtr3d
    eleqtrd
    @66
    @80
    cr
    wcel
    #
    @46
    @84
    @85
    wb
    #
    @66
    @45
    @92
    @78
    @15
    cr
    cr
    xp1st
    syl
    @79
    @92
    @80
    cxr
    wcel
    @16
    cxr
    wcel
    @93
    @46
    @80
    rexr
    @16
    rexr
    @80
    @16
    @62
    elioo2
    syl2an
    syl2anc
    mpbid
    simp3d
    ltled
    letrd
    expr
    exlimdv
    mpd
    wph
    @5
    @36
    ovolicc.3
    adantr
    @17
    @61
    @5
    @42
    @16
    cB
    @16
    @18
    cA
    cle
    breq2
    cB
    @18
    cA
    cle
    breq2
    ifboth
    syl2anc
    @37
    @46
    @59
    @43
    @58
    @60
    @16
    cB
    min2
    syl2anc
    wph
    @40
    @41
    @42
    @43
    w3a
    wb
    #
    @36
    wph
    @67
    @59
    @94
    ovolicc.1
    ovolicc.2
    cA
    cB
    @18
    elicc2
    syl2anc
    adantr
    mpbir3and
    #
    sseldd
    vx
    @18
    cU
    eluni2
    sylib
    @37
    @26
    @26
    vx
    cU
    cT
    @37
    @25
    cU
    wcel
    #
    @26
    wa
    #
    @25
    cT
    wcel
    #
    @26
    wa
    @37
    @97
    wa
    #
    @98
    @26
    @99
    @96
    @25
    @4
    cin
    #
    c0
    wne
    #
    @98
    @37
    @96
    @26
    simprl
    @99
    @26
    @40
    @101
    @37
    @96
    @26
    simprr
    #
    @37
    @40
    @97
    @95
    adantr
    @18
    @25
    @4
    inelcm
    syl2anc
    @35
    @101
    vu
    @25
    cU
    cT
    @33
    @25
    wceq
    @34
    @100
    c0
    @33
    @25
    @4
    ineq1
    neeq1d
    ovolicc2.10
    elrab2
    sylanbrc
    @102
    jca
    ex
    reximdv2
    mpd
    ralrimiva
    @26
    @20
    vt
    vx
    cT
    cT
    vh
    @25
    @19
    @18
    eleq2
    ac6sfi
    syl2anc
    adantr
    @10
    @22
    @2
    vh
    @10
    @12
    @21
    @2
    @21
    @25
    cG
    cfv
    #
    cF
    cfv
    #
    c2nd
    cfv
    #
    cB
    cle
    wbr
    #
    @105
    cB
    cif
    #
    @25
    @11
    cfv
    #
    wcel
    #
    vx
    cT
    wral
    #
    @10
    @12
    wa
    @2
    @109
    @20
    vx
    vt
    cT
    @25
    @13
    wceq
    #
    @107
    @18
    @108
    @19
    @111
    @106
    @17
    @105
    @16
    cB
    @111
    @105
    @16
    cB
    cle
    @111
    @104
    @15
    c2nd
    @111
    @103
    @14
    cF
    @25
    @13
    cG
    fveq2
    fveq2d
    fveq2d
    #
    breq1d
    @112
    ifbieq1d
    @25
    @13
    @11
    fveq2
    eleq12d
    #
    cbvralv
    @10
    @12
    @110
    @2
    wph
    @9
    @12
    @110
    wa
    #
    @2
    wph
    @9
    @114
    wa
    #
    wa
    #
    vu
    vt
    cA
    cB
    @0
    cS
    cT
    cU
    vn
    cF
    cG
    @11
    @11
    c1st
    ccom
    cn
    @0
    csn
    cxp
    c1
    cseq
    #
    cB
    vm
    cv
    #
    @117
    cfv
    #
    wcel
    #
    vm
    cn
    crab
    #
    cr
    clt
    cinf
    #
    @121
    wph
    @67
    @115
    ovolicc.1
    adantr
    wph
    @59
    @115
    ovolicc.2
    adantr
    wph
    @5
    @115
    ovolicc.3
    adantr
    ovolicc2.4
    wph
    @89
    @115
    ovolicc2.5
    adantr
    wph
    @32
    @115
    ovolicc2.6
    adantr
    wph
    @39
    @115
    ovolicc2.7
    adantr
    wph
    @49
    @115
    ovolicc2.8
    adantr
    wph
    @50
    @90
    @115
    ovolicc2.9
    adantlr
    ovolicc2.10
    wph
    @9
    @12
    @110
    simprrl
    @116
    @110
    @36
    @20
    wph
    @9
    @12
    @110
    simprrr
    @109
    @20
    vx
    @13
    cT
    @113
    rspccva
    sylan
    wph
    @8
    @1
    @114
    simprlr
    #
    @116
    @8
    @0
    @4
    cin
    #
    c0
    wne
    #
    @0
    cT
    wcel
    wph
    @8
    @1
    @114
    simprll
    @116
    @1
    @6
    @125
    @123
    wph
    @6
    @115
    @7
    adantr
    cA
    @0
    @4
    inelcm
    syl2anc
    @35
    @125
    vu
    @0
    cU
    cT
    @33
    @0
    wceq
    @34
    @124
    c0
    @33
    @0
    @4
    ineq1
    neeq1d
    ovolicc2.10
    elrab2
    sylanbrc
    @117
    eqid
    @120
    cB
    vn
    cv
    #
    @117
    cfv
    #
    wcel
    vm
    vn
    cn
    @118
    @126
    wceq
    @119
    @127
    cB
    @118
    @126
    @117
    fveq2
    eleq2d
    cbvrabv
    @122
    eqid
    ovolicc2lem4
    anassrs
    expr
    syl5bir
    expimpd
    exlimdv
    mpd
    rexlimddv
end
