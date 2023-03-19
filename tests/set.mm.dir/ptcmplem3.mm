include "cv.mm"
include "cfv.mm"
include "cuni.mm"
include "c1o.mm"
include "cen.mm"
include "wbr.mm"
include "wn.mm"
include "crab.mm"
include "cvv.mm"
include "wf.mm"
include "cdif.mm"
include "wcel.mm"
include "wral.mm"
include "wa.mm"
include "wfn.mm"
include "wex.mm"
include "ciun.mm"
include "ccrd.mm"
include "cdm.mm"
include "wrex.mm"
include "rabexg.mm"
include "syl.mm"
include "wss.mm"
include "ptcmplem2.mm"
include "eldifi.mm"
include "3ad2ant3.mm"
include "rabssdv.mm"
include "ralrimivw.mm"
include "ss2iun.mm"
include "ssnum.mm"
include "syl2anc.mm"
include "elrabi.mm"
include "c0.mm"
include "wceq.mm"
include "cpw.mm"
include "cfn.mm"
include "cin.mm"
include "adantr.mm"
include "ssdif0.mm"
include "ccmp.mm"
include "ffvelrnda.mm"
include "cmpt.mm"
include "ccnv.mm"
include "cima.mm"
include "ssrab2.mm"
include "eqsstri.mm"
include "a1i.mm"
include "simpr.mm"
include "uniss.mm"
include "mp1i.mm"
include "eqssd.mm"
include "eqid.mm"
include "cmpcov.mm"
include "syl3anc.mm"
include "crn.mm"
include "elfpw.mm"
include "simplbi.mm"
include "ad2antrl.mm"
include "sselda.mm"
include "weq.mm"
include "imaeq2.mm"
include "eleq1d.mm"
include "elrab2.mm"
include "simprbi.mm"
include "fmptd.mm"
include "frn.mm"
include "cab.mm"
include "rnmpt.mm"
include "abrexfi.mm"
include "syl5eqel.mm"
include "sylanbrc.mm"
include "simp-4r.mm"
include "cixp.mm"
include "syl6eleq.mm"
include "vex.mm"
include "elixp.mm"
include "fveq2.mm"
include "unieqd.mm"
include "eleq12d.mm"
include "rspcv.mm"
include "sylc.mm"
include "simplrr.mm"
include "eleqtrd.mm"
include "eluni2.mm"
include "sylib.mm"
include "wb.mm"
include "fveq1.mm"
include "mptpreima.mm"
include "baib.mm"
include "ad2antlr.mm"
include "rexbidva.mm"
include "mpbird.mm"
include "eliun.mm"
include "sylibr.mm"
include "ex.mm"
include "ssrdv.mm"
include "ralrimiva.mm"
include "dfiun2g.mm"
include "unieqi.mm"
include "syl6eqr.mm"
include "sseqtrd.mm"
include "unissd.mm"
include "ad3antrrr.mm"
include "sseqtr4d.mm"
include "unieq.mm"
include "eqeq2d.mm"
include "rspcev.mm"
include "rexlimddv.mm"
include "syl5bir.mm"
include "mtod.mm"
include "neq0.mm"
include "rexv.mm"
include "sylan2.mm"
include "eleq1.mm"
include "ac6num.mm"
include "cif.mm"
include "mptexg.mm"
include "fvex.mm"
include "uniex.mm"
include "ifex.mm"
include "rgenw.mm"
include "fnmpt.mm"
include "wi.mm"
include "breq1d.mm"
include "notbid.mm"
include "ralrab.mm"
include "iftrue.mm"
include "ad2antll.mm"
include "adantrr.mm"
include "csn.mm"
include "adantl.mm"
include "en1b.mm"
include "elsni.mm"
include "eqeltrrd.mm"
include "exlimddv.mm"
include "adantlr.mm"
include "eqeltrd.mm"
include "a1d.mm"
include "expr.mm"
include "pm2.27.mm"
include "iffalse.mm"
include "sylibrd.mm"
include "pm2.61d1.mm"
include "ralimdva.mm"
include "syl5bi.mm"
include "impr.mm"
include "fneq1.mm"
include "ifbieq12d.mm"
include "fvmpt.mm"
include "sylan9eq.mm"
include "ralbidva.mm"
include "anbi12d.mm"
include "spcegv.mm"
include "3impib.mm"

theorem ptcmplem3
  let wph: wff ph
  let vz: setvar z
  let vw: setvar w
  let vu: setvar u
  let cA: class A
  let cS: class S
  let cU: class U
  let vf: setvar f
  let vk: setvar k
  let vn: setvar n
  let cF: class F
  let cK: class K
  let cV: class V
  let cX: class X
  let vg: setvar g
  let vm: setvar m
  let vt: setvar t
  let vv: setvar v
  let vx: setvar x
  let vy: setvar y
  assume ptcmp.1: |- S = ( k e. A , u e. ( F ` k ) |-> ( `' ( w e. X |-> ( w ` k ) ) " u ) )
  assume ptcmp.2: |- X = X_ n e. A U. ( F ` n )
  assume ptcmp.3: |- ( ph -> A e. V )
  assume ptcmp.4: |- ( ph -> F : A --> Comp )
  assume ptcmp.5: |- ( ph -> X e. ( UFL i^i dom card ) )
  assume ptcmplem2.5: |- ( ph -> U C_ ran S )
  assume ptcmplem2.6: |- ( ph -> X = U. U )
  assume ptcmplem2.7: |- ( ph -> -. E. z e. ( ~P U i^i Fin ) X = U. z )
  assume ptcmplem3.8: |- K = { u e. ( F ` k ) | ( `' ( w e. X |-> ( w ` k ) ) " u ) e. U }

  disjoint f k
  disjoint f n
  disjoint f u
  disjoint f w
  disjoint f z
  disjoint A f
  disjoint k n
  disjoint k u
  disjoint k w
  disjoint k z
  disjoint A k
  disjoint n u
  disjoint n w
  disjoint n z
  disjoint A n
  disjoint u w
  disjoint u z
  disjoint A u
  disjoint w z
  disjoint A w
  disjoint A z
  disjoint K f
  disjoint K u
  disjoint S k
  disjoint S n
  disjoint S u
  disjoint S z
  disjoint f ph
  disjoint k ph
  disjoint n ph
  disjoint ph u
  disjoint U k
  disjoint U u
  disjoint U z
  disjoint V k
  disjoint V n
  disjoint V u
  disjoint V w
  disjoint V z
  disjoint F f
  disjoint F k
  disjoint F n
  disjoint F u
  disjoint F w
  disjoint F z
  disjoint X f
  disjoint X k
  disjoint X n
  disjoint X u
  disjoint X w
  disjoint X z
  disjoint f g
  disjoint f m
  disjoint f t
  disjoint f v
  disjoint f x
  disjoint f y
  disjoint g k
  disjoint g m
  disjoint g n
  disjoint g t
  disjoint g u
  disjoint g v
  disjoint g w
  disjoint g x
  disjoint g y
  disjoint g z
  disjoint A g
  disjoint k m
  disjoint k t
  disjoint k v
  disjoint k x
  disjoint k y
  disjoint m n
  disjoint m t
  disjoint m u
  disjoint m v
  disjoint m w
  disjoint m x
  disjoint m y
  disjoint m z
  disjoint A m
  disjoint n t
  disjoint n v
  disjoint n x
  disjoint n y
  disjoint t u
  disjoint t v
  disjoint t w
  disjoint t x
  disjoint t y
  disjoint t z
  disjoint A t
  disjoint u v
  disjoint u x
  disjoint u y
  disjoint v w
  disjoint v x
  disjoint v y
  disjoint v z
  disjoint A v
  disjoint w x
  disjoint w y
  disjoint x y
  disjoint x z
  disjoint A x
  disjoint y z
  disjoint A y
  disjoint K g
  disjoint K t
  disjoint K v
  disjoint K x
  disjoint K y
  disjoint S v
  disjoint S y
  disjoint g ph
  disjoint m ph
  disjoint ph t
  disjoint ph v
  disjoint ph x
  disjoint ph y
  disjoint U t
  disjoint U v
  disjoint U x
  disjoint V g
  disjoint V x
  disjoint V y
  disjoint F g
  disjoint F m
  disjoint F t
  disjoint F v
  disjoint F x
  disjoint F y
  disjoint X g
  disjoint X m
  disjoint X t
  disjoint X v
  disjoint X x
  disjoint X y
  assert |- ( ph -> E. f ( f Fn A /\ A. k e. A ( f ` k ) e. ( U. ( F ` k ) \ U. K ) ) )

  proof
    wph
    vn
    cv
    #
    cF
    cfv
    #
    cuni
    #
    c1o
    cen
    wbr
    #
    wn
    #
    vn
    cA
    crab
    #
    cvv
    vg
    cv
    #
    wf
    #
    vk
    cv
    #
    @6
    cfv
    #
    @8
    cF
    cfv
    #
    cuni
    #
    cK
    cuni
    #
    cdif
    #
    wcel
    #
    vk
    @5
    wral
    #
    wa
    #
    vf
    cv
    #
    cA
    wfn
    #
    @8
    @17
    cfv
    #
    @13
    wcel
    #
    vk
    cA
    wral
    #
    wa
    #
    vf
    wex
    #
    vg
    wph
    @5
    cvv
    wcel
    #
    vk
    @5
    vy
    cv
    #
    @13
    wcel
    #
    vy
    cvv
    crab
    #
    ciun
    #
    ccrd
    cdm
    #
    wcel
    #
    @26
    vy
    cvv
    wrex
    #
    vk
    @5
    wral
    @16
    vg
    wex
    wph
    cA
    cV
    wcel
    #
    @24
    ptcmp.3
    @4
    vn
    cA
    cV
    rabexg
    syl
    wph
    vk
    @5
    @11
    ciun
    #
    @29
    wcel
    @28
    @33
    wss
    #
    @30
    wph
    vz
    vw
    vu
    cA
    cS
    cU
    vk
    vn
    cF
    cV
    cX
    ptcmp.1
    ptcmp.2
    ptcmp.3
    ptcmp.4
    ptcmp.5
    ptcmplem2.5
    ptcmplem2.6
    ptcmplem2.7
    ptcmplem2
    wph
    @27
    @11
    wss
    #
    vk
    @5
    wral
    @34
    wph
    @35
    vk
    @5
    wph
    @26
    vy
    cvv
    @11
    @26
    wph
    @25
    @11
    wcel
    #
    @25
    cvv
    wcel
    @25
    @11
    @12
    eldifi
    #
    3ad2ant3
    rabssdv
    ralrimivw
    vk
    @5
    @27
    @11
    ss2iun
    syl
    @33
    @28
    ssnum
    syl2anc
    wph
    @31
    vk
    @5
    @8
    @5
    wcel
    wph
    @8
    cA
    wcel
    #
    @31
    @4
    vn
    @8
    cA
    elrabi
    wph
    @38
    wa
    #
    @26
    vy
    wex
    #
    @31
    @39
    @13
    c0
    wceq
    #
    wn
    @40
    @39
    @41
    cX
    vz
    cv
    #
    cuni
    #
    wceq
    #
    vz
    cU
    cpw
    cfn
    cin
    #
    wrex
    #
    wph
    @46
    wn
    @38
    ptcmplem2.7
    adantr
    @41
    @11
    @12
    wss
    #
    @39
    @46
    @11
    @12
    ssdif0
    @39
    @47
    @46
    @39
    @47
    wa
    #
    @11
    vt
    cv
    #
    cuni
    #
    wceq
    #
    @46
    vt
    cK
    cpw
    cfn
    cin
    #
    @48
    @10
    ccmp
    wcel
    #
    cK
    @10
    wss
    #
    @11
    @12
    wceq
    @51
    vt
    @52
    wrex
    @39
    @53
    @47
    wph
    cA
    ccmp
    @8
    cF
    ptcmp.4
    ffvelrnda
    adantr
    @54
    @48
    cK
    vw
    cX
    @8
    vw
    cv
    #
    cfv
    #
    cmpt
    #
    ccnv
    #
    vu
    cv
    #
    cima
    #
    cU
    wcel
    #
    vu
    @10
    crab
    @10
    ptcmplem3.8
    @61
    vu
    @10
    ssrab2
    eqsstri
    #
    a1i
    @48
    @11
    @12
    @39
    @47
    simpr
    @54
    @12
    @11
    wss
    @48
    @62
    cK
    @10
    uniss
    mp1i
    eqssd
    cK
    @10
    @11
    vt
    @11
    eqid
    cmpcov
    syl3anc
    @48
    @49
    @52
    wcel
    #
    @51
    wa
    #
    wa
    #
    vx
    @49
    @58
    vx
    cv
    #
    cima
    #
    cmpt
    #
    crn
    #
    @45
    wcel
    #
    cX
    @69
    cuni
    #
    wceq
    #
    @46
    @65
    @69
    cU
    wss
    #
    @69
    cfn
    wcel
    #
    @70
    @65
    @49
    cU
    @68
    wf
    @73
    @65
    vx
    @49
    @67
    cU
    @68
    @65
    @66
    @49
    wcel
    #
    wa
    @66
    cK
    wcel
    #
    @67
    cU
    wcel
    #
    @65
    @49
    cK
    @66
    @63
    @49
    cK
    wss
    #
    @48
    @51
    @63
    @78
    @49
    cfn
    wcel
    #
    @49
    cK
    elfpw
    #
    simplbi
    ad2antrl
    sselda
    @76
    @66
    @10
    wcel
    @77
    @61
    @77
    vu
    @66
    @10
    cK
    vu
    vx
    weq
    @60
    @67
    cU
    @59
    @66
    @58
    imaeq2
    eleq1d
    ptcmplem3.8
    elrab2
    simprbi
    syl
    #
    @68
    eqid
    #
    fmptd
    @49
    cU
    @68
    frn
    syl
    #
    @65
    @79
    @74
    @63
    @79
    @48
    @51
    @63
    @78
    @79
    @80
    simprbi
    ad2antrl
    @79
    @69
    @17
    @67
    wceq
    vx
    @49
    wrex
    vf
    cab
    #
    cfn
    vx
    vf
    @49
    @67
    @68
    @82
    rnmpt
    #
    vx
    vf
    @49
    @67
    abrexfi
    syl5eqel
    syl
    @69
    cU
    elfpw
    sylanbrc
    @65
    cX
    @71
    @65
    cX
    vx
    @49
    @67
    ciun
    #
    @71
    @65
    vf
    cX
    @86
    @65
    @17
    cX
    wcel
    #
    @17
    @86
    wcel
    #
    @65
    @87
    wa
    #
    @17
    @67
    wcel
    #
    vx
    @49
    wrex
    #
    @88
    @89
    @91
    @19
    @66
    wcel
    #
    vx
    @49
    wrex
    #
    @89
    @19
    @50
    wcel
    @93
    @89
    @19
    @11
    @50
    @89
    @38
    @0
    @17
    cfv
    #
    @2
    wcel
    #
    vn
    cA
    wral
    #
    @19
    @11
    wcel
    #
    wph
    @38
    @47
    @64
    @87
    simp-4r
    @89
    @17
    vn
    cA
    @2
    cixp
    #
    wcel
    #
    @96
    @89
    @17
    cX
    @98
    @65
    @87
    simpr
    ptcmp.2
    syl6eleq
    @99
    @18
    @96
    vn
    cA
    @2
    @17
    vf
    vex
    elixp
    simprbi
    syl
    @95
    @97
    vn
    @8
    cA
    vn
    vk
    weq
    #
    @94
    @19
    @2
    @11
    @0
    @8
    @17
    fveq2
    @100
    @1
    @10
    @0
    @8
    cF
    fveq2
    unieqd
    #
    eleq12d
    rspcv
    sylc
    @48
    @63
    @51
    @87
    simplrr
    eleqtrd
    vx
    @19
    @49
    eluni2
    sylib
    @89
    @90
    @92
    vx
    @49
    @87
    @90
    @92
    wb
    @65
    @75
    @90
    @87
    @92
    @56
    @66
    wcel
    @92
    vw
    @17
    cX
    @67
    vw
    vf
    weq
    @56
    @19
    @66
    @8
    @55
    @17
    fveq1
    eleq1d
    vw
    cX
    @56
    @66
    @57
    @57
    eqid
    mptpreima
    elrab2
    baib
    ad2antlr
    rexbidva
    mpbird
    vx
    @17
    @49
    @67
    eliun
    sylibr
    ex
    ssrdv
    @65
    @86
    @84
    cuni
    #
    @71
    @65
    @77
    vx
    @49
    wral
    @86
    @102
    wceq
    @65
    @77
    vx
    @49
    @81
    ralrimiva
    vx
    vf
    @49
    @67
    cU
    dfiun2g
    syl
    @69
    @84
    @85
    unieqi
    syl6eqr
    sseqtrd
    @65
    @71
    cU
    cuni
    #
    cX
    @65
    @69
    cU
    @83
    unissd
    wph
    cX
    @103
    wceq
    @38
    @47
    @64
    ptcmplem2.6
    ad3antrrr
    sseqtr4d
    eqssd
    @44
    @72
    vz
    @69
    @45
    @42
    @69
    wceq
    @43
    @71
    cX
    @42
    @69
    unieq
    eqeq2d
    rspcev
    syl2anc
    rexlimddv
    ex
    syl5bir
    mtod
    vy
    @13
    neq0
    sylib
    #
    @26
    vy
    rexv
    sylibr
    sylan2
    ralrimiva
    @26
    @14
    vk
    vy
    @5
    cvv
    vg
    cvv
    @25
    @9
    @13
    eleq1
    ac6num
    syl3anc
    wph
    @16
    wa
    #
    vm
    cA
    vm
    cv
    #
    cF
    cfv
    #
    cuni
    #
    c1o
    cen
    wbr
    #
    @108
    cuni
    #
    @106
    @6
    cfv
    #
    cif
    #
    cmpt
    #
    cvv
    wcel
    #
    @113
    cA
    wfn
    #
    @11
    c1o
    cen
    wbr
    #
    @11
    cuni
    #
    @9
    cif
    #
    @13
    wcel
    #
    vk
    cA
    wral
    #
    @23
    @105
    @32
    @114
    wph
    @32
    @16
    ptcmp.3
    adantr
    vm
    cA
    @112
    cV
    mptexg
    syl
    @112
    cvv
    wcel
    #
    vm
    cA
    wral
    @115
    @105
    @121
    vm
    cA
    @109
    @110
    @111
    @108
    @107
    @106
    cF
    fvex
    uniex
    uniex
    @106
    @6
    fvex
    ifex
    rgenw
    vm
    cA
    @112
    @113
    cvv
    @113
    eqid
    #
    fnmpt
    mp1i
    wph
    @7
    @15
    @120
    @15
    @116
    wn
    #
    @14
    wi
    #
    vk
    cA
    wral
    wph
    @7
    wa
    #
    @120
    @4
    @123
    @14
    vk
    vn
    cA
    @100
    @3
    @116
    @100
    @2
    @11
    c1o
    cen
    @101
    breq1d
    notbid
    ralrab
    @125
    @124
    @119
    vk
    cA
    @125
    @38
    wa
    @116
    @124
    @119
    wi
    #
    @125
    @38
    @116
    @126
    @125
    @38
    @116
    wa
    #
    wa
    #
    @119
    @124
    @128
    @118
    @117
    @13
    @116
    @118
    @117
    wceq
    @125
    @38
    @116
    @117
    @9
    iftrue
    ad2antll
    wph
    @127
    @117
    @13
    wcel
    #
    @7
    wph
    @127
    wa
    #
    @26
    @129
    vy
    wph
    @38
    @40
    @116
    @104
    adantrr
    @130
    @26
    wa
    #
    @25
    @117
    @13
    @131
    @25
    @117
    csn
    #
    wcel
    @25
    @117
    wceq
    @131
    @25
    @11
    @132
    @26
    @36
    @130
    @37
    adantl
    @131
    @116
    @11
    @132
    wceq
    wph
    @38
    @116
    @26
    simplrr
    @11
    en1b
    sylib
    eleqtrd
    @25
    @117
    elsni
    syl
    @130
    @26
    simpr
    eqeltrrd
    exlimddv
    adantlr
    eqeltrd
    a1d
    expr
    @123
    @124
    @14
    @119
    @123
    @14
    pm2.27
    @123
    @118
    @9
    @13
    @116
    @117
    @9
    iffalse
    eleq1d
    sylibrd
    pm2.61d1
    ralimdva
    syl5bi
    impr
    @114
    @115
    @120
    @23
    @22
    @115
    @120
    wa
    vf
    @113
    cvv
    @17
    @113
    wceq
    #
    @18
    @115
    @21
    @120
    cA
    @17
    @113
    fneq1
    @133
    @20
    @119
    vk
    cA
    @133
    @38
    wa
    @19
    @118
    @13
    @133
    @38
    @19
    @8
    @113
    cfv
    @118
    @8
    @17
    @113
    fveq1
    vm
    @8
    @112
    @118
    cA
    @113
    vm
    vk
    weq
    #
    @109
    @116
    @110
    @111
    @117
    @9
    @134
    @108
    @11
    c1o
    cen
    @134
    @107
    @10
    @106
    @8
    cF
    fveq2
    unieqd
    #
    breq1d
    @134
    @108
    @11
    @135
    unieqd
    @106
    @8
    @6
    fveq2
    ifbieq12d
    @122
    @116
    @117
    @9
    @11
    @10
    @8
    cF
    fvex
    uniex
    uniex
    @8
    @6
    fvex
    ifex
    fvmpt
    sylan9eq
    eleq1d
    ralbidva
    anbi12d
    spcegv
    3impib
    syl3anc
    exlimddv
end
