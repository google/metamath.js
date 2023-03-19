include "ctop.mm"
include "wcel.mm"
include "ccmp.mm"
include "cnlly.mm"
include "w3a.mm"
include "cxko.mm"
include "co.mm"
include "ctx.mm"
include "ccn.mm"
include "cxp.mm"
include "wf.mm"
include "ccnv.mm"
include "cv.mm"
include "cima.mm"
include "crest.mm"
include "cuni.mm"
include "cpw.mm"
include "crab.mm"
include "wss.mm"
include "cmpt2.mm"
include "crn.mm"
include "wral.mm"
include "ccom.mm"
include "wa.mm"
include "simprr.mm"
include "simprl.mm"
include "cnco.mm"
include "syl2anc.mm"
include "ralrimivva.mm"
include "fmpt2.mm"
include "sylib.mm"
include "wceq.mm"
include "wrex.mm"
include "cab.mm"
include "eqid.mm"
include "rnmpt2.mm"
include "eleq2i.mm"
include "abid.mm"
include "oveq2.mm"
include "eleq1d.mm"
include "rexrab.mm"
include "3bitri.mm"
include "wi.mm"
include "cfv.mm"
include "wfn.mm"
include "wb.mm"
include "ad2antrr.mm"
include "ffn.mm"
include "elpreima.mm"
include "3syl.mm"
include "cop.mm"
include "coeq1.mm"
include "coeq2.mm"
include "vex.mm"
include "coex.mm"
include "ovmpt2.mm"
include "adantl.mm"
include "imaeq1.mm"
include "sseq1d.mm"
include "elrab.mm"
include "simprbi.mm"
include "simp2.mm"
include "ad3antrrr.mm"
include "elpwi.mm"
include "ad2antrl.mm"
include "simplr.mm"
include "simprll.mm"
include "simprlr.mm"
include "xkococnlem.mm"
include "expr.mm"
include "syl5.mm"
include "sylbid.mm"
include "fveq2.mm"
include "df-ov.mm"
include "syl6eqr.mm"
include "eleq1.mm"
include "anbi1d.mm"
include "rexbidv.mm"
include "imbi12d.mm"
include "ralxp.mm"
include "sylibr.mm"
include "r19.21bi.mm"
include "expimpd.mm"
include "ralrimiv.mm"
include "nllytop.mm"
include "3ad2ant2.mm"
include "simp3.mm"
include "xkotop.mm"
include "simp1.mm"
include "txtop.mm"
include "eltop2.mm"
include "syl.mm"
include "mpbird.mm"
include "imaeq2.mm"
include "syl5ibrcom.mm"
include "rexlimdva.mm"
include "anassrs.mm"
include "syl5bi.mm"
include "cvv.mm"
include "ctopon.mm"
include "xkotopon.mm"
include "txtopon.mm"
include "ovex.mm"
include "pwex.mm"
include "xkotf.mm"
include "frn.mm"
include "ax-mp.mm"
include "ssexi.mm"
include "a1i.mm"
include "cfi.mm"
include "ctg.mm"
include "xkoval.mm"
include "3adant2.mm"
include "subbascn.mm"
include "mpbir2and.mm"

theorem xkococn
  let cR: class R
  let cS: class S
  let cT: class T
  let vf: setvar f
  let vg: setvar g
  let cF: class F
  let va: setvar a
  let vk: setvar k
  let vs: setvar s
  let vu: setvar u
  let vv: setvar v
  let vw: setvar w
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cA: class A
  let vb: setvar b
  let cB: class B
  let wph: wff ph
  let vh: setvar h
  let cK: class K
  let cV: class V
  assume xkococn.1: |- F = ( f e. ( S Cn T ) , g e. ( R Cn S ) |-> ( f o. g ) )

  disjoint f g
  disjoint R f
  disjoint R g
  disjoint S f
  disjoint S g
  disjoint T f
  disjoint T g
  disjoint a k
  disjoint a s
  disjoint a u
  disjoint a v
  disjoint a w
  disjoint a x
  disjoint a y
  disjoint a z
  disjoint A a
  disjoint k s
  disjoint k u
  disjoint k v
  disjoint k w
  disjoint k x
  disjoint k y
  disjoint k z
  disjoint A k
  disjoint s u
  disjoint s v
  disjoint s w
  disjoint s x
  disjoint s y
  disjoint s z
  disjoint A s
  disjoint u v
  disjoint u w
  disjoint u x
  disjoint u y
  disjoint u z
  disjoint A u
  disjoint v w
  disjoint v x
  disjoint v y
  disjoint v z
  disjoint A v
  disjoint w x
  disjoint w y
  disjoint w z
  disjoint A w
  disjoint x y
  disjoint x z
  disjoint A x
  disjoint y z
  disjoint A y
  disjoint A z
  disjoint b k
  disjoint b s
  disjoint b u
  disjoint b v
  disjoint b w
  disjoint b x
  disjoint b y
  disjoint b z
  disjoint B b
  disjoint B k
  disjoint B s
  disjoint B u
  disjoint B v
  disjoint B w
  disjoint B x
  disjoint B y
  disjoint B z
  disjoint k ph
  disjoint ph s
  disjoint ph u
  disjoint ph v
  disjoint ph w
  disjoint ph x
  disjoint a b
  disjoint a f
  disjoint a g
  disjoint a h
  disjoint R a
  disjoint b f
  disjoint b g
  disjoint b h
  disjoint R b
  disjoint f h
  disjoint f k
  disjoint f u
  disjoint f v
  disjoint f w
  disjoint f x
  disjoint f y
  disjoint f z
  disjoint g h
  disjoint g k
  disjoint g u
  disjoint g v
  disjoint g w
  disjoint g x
  disjoint g y
  disjoint g z
  disjoint h k
  disjoint h u
  disjoint h v
  disjoint h w
  disjoint h x
  disjoint h y
  disjoint h z
  disjoint R h
  disjoint R k
  disjoint R u
  disjoint R v
  disjoint R w
  disjoint R x
  disjoint R y
  disjoint R z
  disjoint S a
  disjoint S b
  disjoint f s
  disjoint g s
  disjoint S k
  disjoint S s
  disjoint S u
  disjoint S v
  disjoint S w
  disjoint S x
  disjoint S y
  disjoint S z
  disjoint K b
  disjoint h s
  disjoint K h
  disjoint K k
  disjoint K s
  disjoint K u
  disjoint K v
  disjoint K w
  disjoint K x
  disjoint K y
  disjoint K z
  disjoint T a
  disjoint T b
  disjoint T h
  disjoint T k
  disjoint T u
  disjoint T v
  disjoint T w
  disjoint T x
  disjoint T y
  disjoint T z
  disjoint F a
  disjoint F b
  disjoint F k
  disjoint F u
  disjoint F v
  disjoint F w
  disjoint F x
  disjoint F y
  disjoint F z
  disjoint V a
  disjoint V h
  disjoint V k
  disjoint V s
  disjoint V u
  disjoint V v
  disjoint V w
  disjoint V x
  disjoint V y
  disjoint V z
  assert |- ( ( R e. Top /\ S e. N-Locally Comp /\ T e. Top ) -> F e. ( ( ( T ^ko S ) tX ( S ^ko R ) ) Cn ( T ^ko R ) ) )

  proof
    cR
    ctop
    wcel
    #
    cS
    ccmp
    cnlly
    wcel
    #
    cT
    ctop
    wcel
    #
    w3a
    #
    cF
    cT
    cS
    cxko
    co
    #
    cS
    cR
    cxko
    co
    #
    ctx
    co
    #
    cT
    cR
    cxko
    co
    #
    ccn
    co
    wcel
    cS
    cT
    ccn
    co
    #
    cR
    cS
    ccn
    co
    #
    cxp
    #
    cR
    cT
    ccn
    co
    #
    cF
    wf
    #
    cF
    ccnv
    #
    vx
    cv
    #
    cima
    #
    @6
    wcel
    #
    vx
    vk
    vv
    cR
    vy
    cv
    #
    crest
    co
    #
    ccmp
    wcel
    #
    vy
    cR
    cuni
    #
    cpw
    #
    crab
    #
    cT
    vh
    cv
    #
    vk
    cv
    #
    cima
    #
    vv
    cv
    #
    wss
    #
    vh
    @11
    crab
    #
    cmpt2
    #
    crn
    #
    wral
    @3
    vf
    cv
    #
    vg
    cv
    #
    ccom
    #
    @11
    wcel
    #
    vg
    @9
    wral
    vf
    @8
    wral
    @12
    @3
    @34
    vf
    vg
    @8
    @9
    @3
    @31
    @8
    wcel
    #
    @32
    @9
    wcel
    #
    wa
    wa
    @36
    @35
    @34
    @3
    @35
    @36
    simprr
    @3
    @35
    @36
    simprl
    @32
    @31
    cR
    cS
    cT
    cnco
    syl2anc
    ralrimivva
    vf
    vg
    @8
    @9
    @33
    @11
    cF
    xkococn.1
    fmpt2
    sylib
    #
    @3
    @16
    vx
    @30
    @14
    @30
    wcel
    #
    cR
    @24
    crest
    co
    #
    ccmp
    wcel
    #
    @14
    @28
    wceq
    #
    vv
    cT
    wrex
    #
    wa
    #
    vk
    @21
    wrex
    #
    @3
    @16
    @38
    @14
    @42
    vk
    @22
    wrex
    #
    vx
    cab
    #
    wcel
    @45
    @44
    @30
    @46
    @14
    vk
    vv
    vx
    @22
    cT
    @28
    @29
    @29
    eqid
    #
    rnmpt2
    eleq2i
    @45
    vx
    abid
    @19
    @40
    @42
    vk
    vy
    @21
    @17
    @24
    wceq
    @18
    @39
    ccmp
    @17
    @24
    cR
    crest
    oveq2
    eleq1d
    rexrab
    3bitri
    @3
    @43
    @16
    vk
    @21
    @3
    @24
    @21
    wcel
    #
    wa
    @40
    @42
    @16
    @3
    @48
    @40
    @42
    @16
    wi
    @3
    @48
    @40
    wa
    #
    wa
    #
    @41
    @16
    vv
    cT
    @50
    @26
    cT
    wcel
    #
    wa
    #
    @16
    @41
    @13
    @28
    cima
    #
    @6
    wcel
    #
    @52
    @54
    @17
    vz
    cv
    #
    wcel
    #
    @55
    @53
    wss
    #
    wa
    #
    vz
    @6
    wrex
    #
    vy
    @53
    wral
    #
    @52
    @59
    vy
    @53
    @52
    @17
    @53
    wcel
    #
    @17
    @10
    wcel
    #
    @17
    cF
    cfv
    #
    @28
    wcel
    #
    wa
    #
    @59
    @52
    @12
    cF
    @10
    wfn
    @61
    @65
    wb
    @3
    @12
    @49
    @51
    @37
    ad2antrr
    @10
    @11
    cF
    ffn
    @10
    @17
    @28
    cF
    elpreima
    3syl
    @52
    @62
    @64
    @59
    @52
    @64
    @59
    wi
    #
    vy
    @10
    @52
    va
    cv
    #
    vb
    cv
    #
    cF
    co
    #
    @28
    wcel
    #
    @67
    @68
    cop
    #
    @55
    wcel
    #
    @57
    wa
    #
    vz
    @6
    wrex
    #
    wi
    #
    vb
    @9
    wral
    va
    @8
    wral
    @66
    vy
    @10
    wral
    @52
    @75
    va
    vb
    @8
    @9
    @52
    @67
    @8
    wcel
    #
    @68
    @9
    wcel
    #
    wa
    #
    wa
    #
    @70
    @67
    @68
    ccom
    #
    @28
    wcel
    #
    @74
    @79
    @69
    @80
    @28
    @78
    @69
    @80
    wceq
    @52
    vf
    vg
    @67
    @68
    @8
    @9
    @33
    @80
    cF
    @67
    @32
    ccom
    @31
    @67
    @32
    coeq1
    @32
    @68
    @67
    coeq2
    xkococn.1
    @67
    @68
    va
    vex
    vb
    vex
    coex
    ovmpt2
    adantl
    eleq1d
    @81
    @80
    @24
    cima
    #
    @26
    wss
    #
    @79
    @74
    @81
    @80
    @11
    wcel
    @83
    @27
    @83
    vh
    @80
    @11
    @23
    @80
    wceq
    @25
    @82
    @26
    @23
    @80
    @24
    imaeq1
    sseq1d
    elrab
    simprbi
    @52
    @78
    @83
    @74
    @52
    @78
    @83
    wa
    #
    wa
    vz
    @67
    @68
    cR
    cS
    cT
    vf
    vg
    vh
    cF
    @24
    @26
    xkococn.1
    @3
    @1
    @49
    @51
    @84
    @0
    @1
    @2
    simp2
    ad3antrrr
    @50
    @24
    @20
    wss
    #
    @51
    @84
    @48
    @85
    @3
    @40
    @24
    @20
    elpwi
    ad2antrl
    ad2antrr
    @50
    @40
    @51
    @84
    @3
    @48
    @40
    simprr
    ad2antrr
    @50
    @51
    @84
    simplr
    @52
    @76
    @77
    @83
    simprll
    @52
    @76
    @77
    @83
    simprlr
    @52
    @78
    @83
    simprr
    xkococnlem
    expr
    syl5
    sylbid
    ralrimivva
    @66
    @75
    vy
    va
    vb
    @8
    @9
    @17
    @71
    wceq
    #
    @64
    @70
    @59
    @74
    @86
    @63
    @69
    @28
    @86
    @63
    @71
    cF
    cfv
    @69
    @17
    @71
    cF
    fveq2
    @67
    @68
    cF
    df-ov
    syl6eqr
    eleq1d
    @86
    @58
    @73
    vz
    @6
    @86
    @56
    @72
    @57
    @17
    @71
    @55
    eleq1
    anbi1d
    rexbidv
    imbi12d
    ralxp
    sylibr
    r19.21bi
    expimpd
    sylbid
    ralrimiv
    @52
    @6
    ctop
    wcel
    #
    @54
    @60
    wb
    @3
    @87
    @49
    @51
    @3
    @4
    ctop
    wcel
    #
    @5
    ctop
    wcel
    #
    @87
    @3
    cS
    ctop
    wcel
    #
    @2
    @88
    @1
    @0
    @90
    @2
    ccmp
    cS
    nllytop
    3ad2ant2
    #
    @0
    @1
    @2
    simp3
    #
    cS
    cT
    xkotop
    syl2anc
    @3
    @0
    @90
    @89
    @0
    @1
    @2
    simp1
    #
    @91
    cR
    cS
    xkotop
    syl2anc
    @4
    @5
    txtop
    syl2anc
    ad2antrr
    vy
    vz
    @53
    @6
    eltop2
    syl
    mpbird
    @41
    @15
    @53
    @6
    @14
    @28
    @13
    imaeq2
    eleq1d
    syl5ibrcom
    rexlimdva
    anassrs
    expimpd
    rexlimdva
    syl5bi
    ralrimiv
    @3
    vx
    @30
    cF
    @6
    @7
    cvv
    @10
    @11
    @3
    @4
    @8
    ctopon
    cfv
    wcel
    #
    @5
    @9
    ctopon
    cfv
    wcel
    #
    @6
    @10
    ctopon
    cfv
    wcel
    @3
    @90
    @2
    @94
    @91
    @92
    cS
    cT
    @4
    @4
    eqid
    xkotopon
    syl2anc
    @3
    @0
    @90
    @95
    @93
    @91
    cR
    cS
    @5
    @5
    eqid
    xkotopon
    syl2anc
    @4
    @5
    @8
    @9
    txtopon
    syl2anc
    @30
    cvv
    wcel
    @3
    @30
    @11
    cpw
    #
    @11
    cR
    cT
    ccn
    ovex
    pwex
    @22
    cT
    cxp
    #
    @96
    @29
    wf
    @30
    @96
    wss
    vy
    vv
    cR
    cT
    @29
    vh
    vk
    @22
    @20
    @20
    eqid
    #
    @22
    eqid
    #
    @47
    xkotf
    @97
    @96
    @29
    frn
    ax-mp
    ssexi
    a1i
    @0
    @2
    @7
    @30
    cfi
    cfv
    ctg
    cfv
    wceq
    @1
    vy
    vv
    cR
    cT
    @29
    vh
    vk
    @22
    @20
    @98
    @99
    @47
    xkoval
    3adant2
    @0
    @2
    @7
    @11
    ctopon
    cfv
    wcel
    @1
    cR
    cT
    @7
    @7
    eqid
    xkotopon
    3adant2
    subbascn
    mpbir2and
end
