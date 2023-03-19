include "cv.mm"
include "wceq.mm"
include "cin.mm"
include "csb.mm"
include "c0.mm"
include "wo.mm"
include "cxp.mm"
include "wral.mm"
include "wdisj.mm"
include "wcel.mm"
include "wa.mm"
include "c1st.mm"
include "cfv.mm"
include "c2nd.mm"
include "xp1st.mm"
include "ad2antrl.mm"
include "ad2antll.mm"
include "simpl.mm"
include "disjors.mm"
include "sylib.mm"
include "eqeq1.mm"
include "csbeq1.mm"
include "ineq1d.mm"
include "eqeq1d.mm"
include "orbi12d.mm"
include "eqeq2.mm"
include "ineq2d.mm"
include "rspc2v.mm"
include "syl5.mm"
include "imp.mm"
include "syl21anc.mm"
include "xp2nd.mm"
include "jca.mm"
include "anddi.mm"
include "orass.mm"
include "wb.mm"
include "xpopth.mm"
include "adantl.mm"
include "biimpd.mm"
include "wi.mm"
include "wss.mm"
include "inss2.mm"
include "csbin.mm"
include "ineq12i.mm"
include "in4.mm"
include "eqtri.mm"
include "cvv.mm"
include "vex.mm"
include "csbnestg.mm"
include "ax-mp.mm"
include "fvex.mm"
include "csbie.mm"
include "csbeq2i.mm"
include "csbfv.mm"
include "3eqtr3ri.mm"
include "3sstr4i.mm"
include "sseq0.mm"
include "mpan.mm"
include "a1i.mm"
include "adantld.mm"
include "inss1.mm"
include "adantrd.mm"
include "jaod.mm"
include "orim12d.mm"
include "mpd.mm"
include "ralrimivva.mm"
include "sylibr.mm"

theorem disjxpin
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cE: class E
  let cF: class F
  let vp: setvar p
  let va: setvar a
  let vc: setvar c
  let vq: setvar q
  let vr: setvar r
  let vb: setvar b
  let vd: setvar d
  assume disjxpin.1: |- ( x = ( 1st ` p ) -> C = E )
  assume disjxpin.2: |- ( y = ( 2nd ` p ) -> D = F )
  assume disjxpin.3: |- ( ph -> Disj_ x e. A C )
  assume disjxpin.4: |- ( ph -> Disj_ y e. B D )

  disjoint p x
  disjoint A p
  disjoint A x
  disjoint p y
  disjoint B p
  disjoint B y
  disjoint C p
  disjoint D p
  disjoint E x
  disjoint F y
  disjoint a c
  disjoint a p
  disjoint a q
  disjoint a r
  disjoint a x
  disjoint A a
  disjoint c p
  disjoint c q
  disjoint c r
  disjoint c x
  disjoint A c
  disjoint p q
  disjoint p r
  disjoint q r
  disjoint q x
  disjoint A q
  disjoint r x
  disjoint A r
  disjoint b d
  disjoint b p
  disjoint b q
  disjoint b r
  disjoint b y
  disjoint B b
  disjoint d p
  disjoint d q
  disjoint d r
  disjoint d y
  disjoint B d
  disjoint q y
  disjoint B q
  disjoint r y
  disjoint B r
  disjoint C a
  disjoint C c
  disjoint D b
  disjoint D d
  disjoint E q
  disjoint E r
  disjoint F q
  disjoint F r
  disjoint ph q
  disjoint ph r
  assert |- ( ph -> Disj_ p e. ( A X. B ) ( E i^i F ) )

  proof
    wph
    vq
    cv
    #
    vr
    cv
    #
    wceq
    #
    vp
    @0
    cE
    cF
    cin
    #
    csb
    #
    vp
    @1
    @3
    csb
    #
    cin
    #
    c0
    wceq
    #
    wo
    #
    vr
    cA
    cB
    cxp
    #
    wral
    vq
    @9
    wral
    vp
    @9
    @3
    wdisj
    wph
    @8
    vq
    vr
    @9
    @9
    wph
    @0
    @9
    wcel
    #
    @1
    @9
    wcel
    #
    wa
    #
    wa
    #
    @0
    c1st
    cfv
    #
    @1
    c1st
    cfv
    #
    wceq
    #
    @0
    c2nd
    cfv
    #
    @1
    c2nd
    cfv
    #
    wceq
    #
    wa
    #
    @16
    vy
    @17
    cD
    csb
    #
    vy
    @18
    cD
    csb
    #
    cin
    #
    c0
    wceq
    #
    wa
    #
    vx
    @14
    cC
    csb
    #
    vx
    @15
    cC
    csb
    #
    cin
    #
    c0
    wceq
    #
    @19
    wa
    #
    @29
    @24
    wa
    #
    wo
    #
    wo
    #
    wo
    #
    @8
    @13
    @20
    @25
    wo
    @32
    wo
    #
    @34
    @13
    @16
    @29
    wo
    #
    @19
    @24
    wo
    #
    wa
    @35
    @13
    @36
    @37
    @13
    @14
    cA
    wcel
    #
    @15
    cA
    wcel
    #
    wph
    @36
    @10
    @38
    wph
    @11
    @0
    cA
    cB
    xp1st
    ad2antrl
    @11
    @39
    wph
    @10
    @1
    cA
    cB
    xp1st
    ad2antll
    wph
    @12
    simpl
    #
    @38
    @39
    wa
    #
    wph
    @36
    wph
    va
    cv
    #
    vc
    cv
    #
    wceq
    #
    vx
    @42
    cC
    csb
    #
    vx
    @43
    cC
    csb
    #
    cin
    #
    c0
    wceq
    #
    wo
    #
    vc
    cA
    wral
    va
    cA
    wral
    #
    @41
    @36
    wph
    vx
    cA
    cC
    wdisj
    @50
    disjxpin.3
    vx
    cA
    cC
    va
    vc
    disjors
    sylib
    @49
    @36
    @14
    @43
    wceq
    #
    @26
    @46
    cin
    #
    c0
    wceq
    #
    wo
    va
    vc
    @14
    @15
    cA
    cA
    @42
    @14
    wceq
    #
    @44
    @51
    @48
    @53
    @42
    @14
    @43
    eqeq1
    @54
    @47
    @52
    c0
    @54
    @45
    @26
    @46
    vx
    @42
    @14
    cC
    csbeq1
    ineq1d
    eqeq1d
    orbi12d
    @43
    @15
    wceq
    #
    @51
    @16
    @53
    @29
    @43
    @15
    @14
    eqeq2
    @55
    @52
    @28
    c0
    @55
    @46
    @27
    @26
    vx
    @43
    @15
    cC
    csbeq1
    ineq2d
    eqeq1d
    orbi12d
    rspc2v
    syl5
    imp
    syl21anc
    @13
    @17
    cB
    wcel
    #
    @18
    cB
    wcel
    #
    wph
    @37
    @10
    @56
    wph
    @11
    @0
    cA
    cB
    xp2nd
    ad2antrl
    @11
    @57
    wph
    @10
    @1
    cA
    cB
    xp2nd
    ad2antll
    @40
    @56
    @57
    wa
    #
    wph
    @37
    wph
    vb
    cv
    #
    vd
    cv
    #
    wceq
    #
    vy
    @59
    cD
    csb
    #
    vy
    @60
    cD
    csb
    #
    cin
    #
    c0
    wceq
    #
    wo
    #
    vd
    cB
    wral
    vb
    cB
    wral
    #
    @58
    @37
    wph
    vy
    cB
    cD
    wdisj
    @67
    disjxpin.4
    vy
    cB
    cD
    vb
    vd
    disjors
    sylib
    @66
    @37
    @17
    @60
    wceq
    #
    @21
    @63
    cin
    #
    c0
    wceq
    #
    wo
    vb
    vd
    @17
    @18
    cB
    cB
    @59
    @17
    wceq
    #
    @61
    @68
    @65
    @70
    @59
    @17
    @60
    eqeq1
    @71
    @64
    @69
    c0
    @71
    @62
    @21
    @63
    vy
    @59
    @17
    cD
    csbeq1
    ineq1d
    eqeq1d
    orbi12d
    @60
    @18
    wceq
    #
    @68
    @19
    @70
    @24
    @60
    @18
    @17
    eqeq2
    @72
    @69
    @23
    c0
    @72
    @63
    @22
    @21
    vy
    @60
    @18
    cD
    csbeq1
    ineq2d
    eqeq1d
    orbi12d
    rspc2v
    syl5
    imp
    syl21anc
    jca
    @16
    @29
    @19
    @24
    anddi
    sylib
    @20
    @25
    @32
    orass
    sylib
    @13
    @20
    @2
    @33
    @7
    @13
    @20
    @2
    @12
    @20
    @2
    wb
    wph
    @0
    @1
    cA
    cB
    cA
    cB
    xpopth
    adantl
    biimpd
    @13
    @25
    @7
    @32
    @13
    @24
    @7
    @16
    @24
    @7
    wi
    @13
    @6
    @23
    wss
    @24
    @7
    vp
    @0
    cE
    csb
    #
    vp
    @1
    cE
    csb
    #
    cin
    #
    vp
    @0
    cF
    csb
    #
    vp
    @1
    cF
    csb
    #
    cin
    #
    cin
    #
    @78
    @6
    @23
    @75
    @78
    inss2
    @6
    @73
    @76
    cin
    #
    @74
    @77
    cin
    #
    cin
    @79
    @4
    @80
    @5
    @81
    vp
    @0
    cE
    cF
    csbin
    vp
    @1
    cE
    cF
    csbin
    ineq12i
    @73
    @76
    @74
    @77
    in4
    eqtri
    #
    @21
    @76
    @22
    @77
    vp
    @0
    vy
    vp
    cv
    #
    c2nd
    cfv
    #
    cD
    csb
    #
    csb
    #
    vy
    vp
    @0
    @84
    csb
    #
    cD
    csb
    #
    @76
    @21
    @0
    cvv
    wcel
    #
    @86
    @88
    wceq
    vq
    vex
    #
    vp
    vy
    @0
    @84
    cD
    cvv
    csbnestg
    ax-mp
    vp
    @0
    @85
    cF
    vy
    @84
    cD
    cF
    @83
    c2nd
    fvex
    disjxpin.2
    csbie
    #
    csbeq2i
    @87
    @17
    wceq
    @88
    @21
    wceq
    vp
    @0
    c2nd
    csbfv
    vy
    @87
    @17
    cD
    csbeq1
    ax-mp
    3eqtr3ri
    vp
    @1
    @85
    csb
    #
    vy
    vp
    @1
    @84
    csb
    #
    cD
    csb
    #
    @77
    @22
    @1
    cvv
    wcel
    #
    @92
    @94
    wceq
    vr
    vex
    #
    vp
    vy
    @1
    @84
    cD
    cvv
    csbnestg
    ax-mp
    vp
    @1
    @85
    cF
    @91
    csbeq2i
    @93
    @18
    wceq
    @94
    @22
    wceq
    vp
    @1
    c2nd
    csbfv
    vy
    @93
    @18
    cD
    csbeq1
    ax-mp
    3eqtr3ri
    ineq12i
    3sstr4i
    @6
    @23
    sseq0
    mpan
    a1i
    #
    adantld
    @13
    @30
    @7
    @31
    @13
    @29
    @7
    @19
    @29
    @7
    wi
    @13
    @6
    @28
    wss
    @29
    @7
    @79
    @75
    @6
    @28
    @75
    @78
    inss1
    @82
    @26
    @73
    @27
    @74
    vp
    @0
    vx
    @83
    c1st
    cfv
    #
    cC
    csb
    #
    csb
    #
    vx
    vp
    @0
    @98
    csb
    #
    cC
    csb
    #
    @73
    @26
    @89
    @100
    @102
    wceq
    @90
    vp
    vx
    @0
    @98
    cC
    cvv
    csbnestg
    ax-mp
    vp
    @0
    @99
    cE
    vx
    @98
    cC
    cE
    @83
    c1st
    fvex
    disjxpin.1
    csbie
    #
    csbeq2i
    @101
    @14
    wceq
    @102
    @26
    wceq
    vp
    @0
    c1st
    csbfv
    vx
    @101
    @14
    cC
    csbeq1
    ax-mp
    3eqtr3ri
    vp
    @1
    @99
    csb
    #
    vx
    vp
    @1
    @98
    csb
    #
    cC
    csb
    #
    @74
    @27
    @95
    @104
    @106
    wceq
    @96
    vp
    vx
    @1
    @98
    cC
    cvv
    csbnestg
    ax-mp
    vp
    @1
    @99
    cE
    @103
    csbeq2i
    @105
    @15
    wceq
    @106
    @27
    wceq
    vp
    @1
    c1st
    csbfv
    vx
    @105
    @15
    cC
    csbeq1
    ax-mp
    3eqtr3ri
    ineq12i
    3sstr4i
    @6
    @28
    sseq0
    mpan
    a1i
    adantrd
    @13
    @24
    @7
    @29
    @97
    adantld
    jaod
    jaod
    orim12d
    mpd
    ralrimivva
    vp
    @9
    @3
    vq
    vr
    disjors
    sylibr
end
