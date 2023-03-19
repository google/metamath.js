include "cv.mm"
include "cdprd.mm"
include "cdm.mm"
include "wbr.mm"
include "co.mm"
include "wceq.mm"
include "wa.mm"
include "wf.mm"
include "w3a.mm"
include "cword.mm"
include "wrex.mm"
include "wcel.mm"
include "wex.mm"
include "cz.mm"
include "cfv.mm"
include "cmpt.mm"
include "crn.mm"
include "wral.mm"
include "cfn.mm"
include "cc0.mm"
include "chash.mm"
include "cfzo.mm"
include "wrdf.mm"
include "ad2antlr.mm"
include "fdm.mm"
include "syl.mm"
include "fzofi.mm"
include "syl6eqel.mm"
include "wss.mm"
include "csubg.mm"
include "feq2d.mm"
include "mpbird.mm"
include "ffvelrnda.mm"
include "cress.mm"
include "ccyg.mm"
include "cpgp.mm"
include "cin.mm"
include "oveq2.mm"
include "eleq1d.mm"
include "elrab2.mm"
include "simplbi.mm"
include "subgss.mm"
include "cmg.mm"
include "cbs.mm"
include "inss1.mm"
include "simprbi.mm"
include "sseldi.mm"
include "cgrp.mm"
include "eqid.mm"
include "iscyg.mm"
include "subgbas.mm"
include "rexeqdv.mm"
include "ad2antrr.mm"
include "simpr.mm"
include "simplr.mm"
include "subgmulg.mm"
include "syl3anc.mm"
include "mpteq2dva.mm"
include "rneqd.mm"
include "adantr.mm"
include "eqeq12d.mm"
include "rexbidva.mm"
include "ssrexv.mm"
include "sylc.mm"
include "ralrimiva.mm"
include "mpteq2dv.mm"
include "eqeq1d.mm"
include "ac6sfi.mm"
include "syl2anc.mm"
include "simprl.mm"
include "mpbid.mm"
include "iswrdi.mm"
include "eqtr4d.mm"
include "eleq2d.mm"
include "biimpa.mm"
include "simprr.mm"
include "simpl.mm"
include "fveq2d.mm"
include "oveq2d.mm"
include "fveq2.mm"
include "rspccva.mm"
include "sylan.mm"
include "eqeltrd.mm"
include "syldan.mm"
include "cbvmptv.mm"
include "eqtri.mm"
include "fmptd.mm"
include "raleqdv.mm"
include "mpteq12.mm"
include "syl5eq.mm"
include "dprdf.mm"
include "feqmptd.mm"
include "breqtrrd.mm"
include "simplrr.mm"
include "eqtrd.mm"
include "3jca.mm"
include "jca.mm"
include "ex.mm"
include "eximdv.mm"
include "mpd.mm"
include "df-rex.mm"
include "sylibr.mm"
include "ablfac.mm"
include "r19.29a.mm"

theorem ablfac2
  let wph: wff ph
  let vw: setvar w
  let cB: class B
  let cC: class C
  let cS: class S
  let c.x: class .x.
  let vk: setvar k
  let vn: setvar n
  let cG: class G
  let vr: setvar r
  let va: setvar a
  let vb: setvar b
  let vc: setvar c
  let vf: setvar f
  let vh: setvar h
  let vp: setvar p
  let vq: setvar q
  let vs: setvar s
  let vt: setvar t
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cA: class A
  let cF: class F
  let vg: setvar g
  let vj: setvar j
  let cO: class O
  let cW: class W
  let cH: class H
  let cU: class U
  assume ablfac.b: |- B = ( Base ` G )
  assume ablfac.c: |- C = { r e. ( SubGrp ` G ) | ( G |`s r ) e. ( CycGrp i^i ran pGrp ) }
  assume ablfac.1: |- ( ph -> G e. Abel )
  assume ablfac.2: |- ( ph -> B e. Fin )
  assume ablfac2.m: |- .x. = ( .g ` G )
  assume ablfac2.s: |- S = ( k e. dom w |-> ran ( n e. ZZ |-> ( n .x. ( w ` k ) ) ) )

  disjoint S r
  disjoint k n
  disjoint k r
  disjoint k w
  disjoint B k
  disjoint n r
  disjoint n w
  disjoint B n
  disjoint r w
  disjoint B r
  disjoint B w
  disjoint .x. k
  disjoint .x. w
  disjoint C k
  disjoint C n
  disjoint C w
  disjoint k ph
  disjoint n ph
  disjoint ph w
  disjoint G k
  disjoint G n
  disjoint G r
  disjoint G w
  disjoint a b
  disjoint a c
  disjoint a f
  disjoint a h
  disjoint a p
  disjoint a q
  disjoint a s
  disjoint a t
  disjoint a x
  disjoint a y
  disjoint a z
  disjoint A a
  disjoint b c
  disjoint b f
  disjoint b h
  disjoint b p
  disjoint b q
  disjoint b s
  disjoint b t
  disjoint b x
  disjoint b y
  disjoint b z
  disjoint A b
  disjoint c f
  disjoint c h
  disjoint c p
  disjoint c q
  disjoint c s
  disjoint c t
  disjoint c x
  disjoint c y
  disjoint c z
  disjoint A c
  disjoint f h
  disjoint f p
  disjoint f q
  disjoint f s
  disjoint f t
  disjoint f x
  disjoint f y
  disjoint f z
  disjoint A f
  disjoint h p
  disjoint h q
  disjoint h s
  disjoint h t
  disjoint h x
  disjoint h y
  disjoint h z
  disjoint A h
  disjoint p q
  disjoint p s
  disjoint p t
  disjoint p x
  disjoint p y
  disjoint p z
  disjoint A p
  disjoint q s
  disjoint q t
  disjoint q x
  disjoint q y
  disjoint q z
  disjoint A q
  disjoint s t
  disjoint s x
  disjoint s y
  disjoint s z
  disjoint A s
  disjoint t x
  disjoint t y
  disjoint t z
  disjoint A t
  disjoint x y
  disjoint x z
  disjoint A x
  disjoint y z
  disjoint A y
  disjoint A z
  disjoint F s
  disjoint F z
  disjoint a g
  disjoint a r
  disjoint S a
  disjoint b g
  disjoint b r
  disjoint S b
  disjoint c g
  disjoint c r
  disjoint S c
  disjoint f g
  disjoint f r
  disjoint S f
  disjoint g h
  disjoint g q
  disjoint g r
  disjoint g s
  disjoint g t
  disjoint g y
  disjoint S g
  disjoint h r
  disjoint S h
  disjoint q r
  disjoint S q
  disjoint r s
  disjoint r t
  disjoint r y
  disjoint S s
  disjoint S t
  disjoint S y
  disjoint a j
  disjoint a k
  disjoint a n
  disjoint a w
  disjoint B a
  disjoint b j
  disjoint b k
  disjoint b n
  disjoint b w
  disjoint B b
  disjoint c j
  disjoint c k
  disjoint c n
  disjoint c w
  disjoint B c
  disjoint f j
  disjoint f k
  disjoint f n
  disjoint f w
  disjoint B f
  disjoint g j
  disjoint g k
  disjoint g n
  disjoint g p
  disjoint g w
  disjoint g x
  disjoint B g
  disjoint h j
  disjoint h k
  disjoint h n
  disjoint h w
  disjoint B h
  disjoint j k
  disjoint j n
  disjoint j p
  disjoint j r
  disjoint j s
  disjoint j t
  disjoint j w
  disjoint j x
  disjoint B j
  disjoint k p
  disjoint k s
  disjoint k t
  disjoint k x
  disjoint n p
  disjoint n s
  disjoint n t
  disjoint n x
  disjoint p r
  disjoint p w
  disjoint B p
  disjoint r x
  disjoint s w
  disjoint B s
  disjoint t w
  disjoint B t
  disjoint w x
  disjoint B x
  disjoint O b
  disjoint O c
  disjoint O p
  disjoint O x
  disjoint .x. j
  disjoint .x. x
  disjoint C a
  disjoint C b
  disjoint C c
  disjoint C f
  disjoint g z
  disjoint C g
  disjoint C h
  disjoint j q
  disjoint j y
  disjoint j z
  disjoint C j
  disjoint k q
  disjoint k y
  disjoint k z
  disjoint n q
  disjoint n y
  disjoint n z
  disjoint C p
  disjoint q w
  disjoint C q
  disjoint C s
  disjoint C t
  disjoint w y
  disjoint w z
  disjoint C x
  disjoint C y
  disjoint C z
  disjoint W a
  disjoint W b
  disjoint W c
  disjoint W f
  disjoint W h
  disjoint W p
  disjoint W q
  disjoint W t
  disjoint W w
  disjoint W x
  disjoint W y
  disjoint H s
  disjoint a ph
  disjoint b ph
  disjoint c ph
  disjoint f ph
  disjoint h ph
  disjoint j ph
  disjoint p ph
  disjoint ph q
  disjoint ph s
  disjoint ph t
  disjoint ph x
  disjoint ph y
  disjoint ph z
  disjoint U g
  disjoint U s
  disjoint G a
  disjoint G b
  disjoint G c
  disjoint G g
  disjoint G j
  disjoint G p
  disjoint r z
  disjoint G s
  disjoint G t
  disjoint G x
  disjoint G y
  disjoint G z
  assert |- ( ph -> E. w e. Word B ( S : dom w --> C /\ G dom DProd S /\ ( G DProd S ) = B ) )

  proof
    wph
    cG
    vs
    cv
    #
    cdprd
    cdm
    #
    wbr
    #
    cG
    @0
    cdprd
    co
    #
    cB
    wceq
    #
    wa
    #
    vw
    cv
    #
    cdm
    #
    cC
    cS
    wf
    #
    cG
    cS
    @1
    wbr
    #
    cG
    cS
    cdprd
    co
    #
    cB
    wceq
    #
    w3a
    #
    vw
    cB
    cword
    #
    wrex
    #
    vs
    cC
    cword
    #
    wph
    @0
    @15
    wcel
    #
    wa
    #
    @5
    wa
    #
    @6
    @13
    wcel
    #
    @12
    wa
    #
    vw
    wex
    #
    @14
    @18
    @0
    cdm
    #
    cB
    @6
    wf
    #
    vn
    cz
    vn
    cv
    #
    vk
    cv
    #
    @6
    cfv
    #
    c.x
    co
    #
    cmpt
    #
    crn
    #
    @25
    @0
    cfv
    #
    wceq
    #
    vk
    @22
    wral
    #
    wa
    #
    vw
    wex
    #
    @21
    @18
    @22
    cfn
    wcel
    vn
    cz
    @24
    vx
    cv
    #
    c.x
    co
    #
    cmpt
    #
    crn
    #
    @30
    wceq
    #
    vx
    cB
    wrex
    #
    vk
    @22
    wral
    @34
    @18
    @22
    cc0
    @0
    chash
    cfv
    #
    cfzo
    co
    #
    cfn
    @18
    @42
    cC
    @0
    wf
    #
    @22
    @42
    wceq
    #
    @16
    @43
    wph
    @5
    cC
    @0
    wrdf
    ad2antlr
    #
    @42
    cC
    @0
    fdm
    syl
    #
    cc0
    @41
    fzofi
    syl6eqel
    @18
    @40
    vk
    @22
    @18
    @25
    @22
    wcel
    wa
    #
    @30
    cB
    wss
    #
    @39
    vx
    @30
    wrex
    #
    @40
    @47
    @30
    cG
    csubg
    cfv
    #
    wcel
    #
    @48
    @47
    @30
    cC
    wcel
    #
    @51
    @18
    @22
    cC
    @25
    @0
    @18
    @22
    cC
    @0
    wf
    #
    @43
    @45
    @18
    @22
    @42
    cC
    @0
    @46
    feq2d
    mpbird
    #
    ffvelrnda
    #
    @52
    @51
    cG
    @30
    cress
    co
    #
    ccyg
    cpgp
    crn
    #
    cin
    #
    wcel
    #
    cG
    vr
    cv
    #
    cress
    co
    #
    @58
    wcel
    @59
    vr
    @30
    @50
    cC
    @60
    @30
    wceq
    @61
    @56
    @58
    @60
    @30
    cG
    cress
    oveq2
    eleq1d
    ablfac.c
    elrab2
    #
    simplbi
    syl
    #
    cB
    @30
    cG
    ablfac.b
    subgss
    syl
    @47
    @49
    vn
    cz
    @24
    @35
    @56
    cmg
    cfv
    #
    co
    #
    cmpt
    #
    crn
    #
    @56
    cbs
    cfv
    #
    wceq
    #
    vx
    @30
    wrex
    #
    @47
    @70
    @69
    vx
    @68
    wrex
    #
    @47
    @56
    ccyg
    wcel
    #
    @71
    @47
    @58
    ccyg
    @56
    ccyg
    @57
    inss1
    @47
    @52
    @59
    @55
    @52
    @51
    @59
    @62
    simprbi
    syl
    sseldi
    @72
    @56
    cgrp
    wcel
    @71
    vx
    @68
    @64
    vn
    @56
    @68
    eqid
    @64
    eqid
    #
    iscyg
    simprbi
    syl
    @47
    @69
    vx
    @30
    @68
    @47
    @51
    @30
    @68
    wceq
    #
    @63
    @30
    cG
    @56
    @56
    eqid
    #
    subgbas
    syl
    #
    rexeqdv
    mpbird
    @47
    @39
    @69
    vx
    @30
    @47
    @35
    @30
    wcel
    #
    wa
    #
    @38
    @67
    @30
    @68
    @78
    @37
    @66
    @78
    vn
    cz
    @36
    @65
    @78
    @24
    cz
    wcel
    #
    wa
    @51
    @79
    @77
    @36
    @65
    wceq
    @47
    @51
    @77
    @79
    @63
    ad2antrr
    @78
    @79
    simpr
    @47
    @77
    @79
    simplr
    @30
    @64
    c.x
    cG
    @56
    @24
    @35
    ablfac2.m
    @75
    @73
    subgmulg
    syl3anc
    mpteq2dva
    rneqd
    @47
    @74
    @77
    @76
    adantr
    eqeq12d
    rexbidva
    mpbird
    @39
    vx
    @30
    cB
    ssrexv
    sylc
    ralrimiva
    @39
    @31
    vk
    vx
    @22
    cB
    vw
    @35
    @26
    wceq
    #
    @38
    @29
    @30
    @80
    @37
    @28
    @80
    vn
    cz
    @36
    @27
    @35
    @26
    @24
    c.x
    oveq2
    mpteq2dv
    rneqd
    eqeq1d
    ac6sfi
    syl2anc
    @18
    @33
    @20
    vw
    @18
    @33
    @20
    @18
    @33
    wa
    #
    @19
    @12
    @81
    @42
    cB
    @6
    wf
    #
    @19
    @81
    @23
    @82
    @18
    @23
    @32
    simprl
    @81
    @22
    @42
    cB
    @6
    @18
    @44
    @33
    @46
    adantr
    #
    feq2d
    mpbid
    #
    cB
    @41
    @6
    iswrdi
    syl
    @81
    @8
    @9
    @11
    @81
    vj
    @7
    vn
    cz
    @24
    vj
    cv
    #
    @6
    cfv
    #
    c.x
    co
    #
    cmpt
    #
    crn
    #
    cC
    cS
    @81
    @85
    @7
    wcel
    #
    @85
    @22
    wcel
    #
    @89
    cC
    wcel
    @81
    @90
    @91
    @81
    @7
    @22
    @85
    @81
    @7
    @42
    @22
    @81
    @82
    @7
    @42
    wceq
    @84
    @42
    cB
    @6
    fdm
    syl
    @83
    eqtr4d
    #
    eleq2d
    biimpa
    @81
    @91
    wa
    @89
    @85
    @0
    cfv
    #
    cC
    @81
    @32
    @91
    @89
    @93
    wceq
    #
    @18
    @23
    @32
    simprr
    #
    @31
    @94
    vk
    @85
    @22
    @25
    @85
    wceq
    #
    @29
    @89
    @30
    @93
    @96
    @28
    @88
    @96
    vn
    cz
    @27
    @87
    @96
    @79
    wa
    #
    @26
    @86
    @24
    c.x
    @97
    @25
    @85
    @6
    @96
    @79
    simpl
    fveq2d
    oveq2d
    mpteq2dva
    rneqd
    @25
    @85
    @0
    fveq2
    eqeq12d
    rspccva
    sylan
    @81
    @22
    cC
    @85
    @0
    @18
    @53
    @33
    @54
    adantr
    ffvelrnda
    eqeltrd
    syldan
    cS
    vk
    @7
    @29
    cmpt
    #
    vj
    @7
    @89
    cmpt
    ablfac2.s
    vk
    vj
    @7
    @29
    @89
    @96
    @28
    @88
    @96
    vn
    cz
    @27
    @87
    @96
    @26
    @86
    @24
    c.x
    @25
    @85
    @6
    fveq2
    oveq2d
    mpteq2dv
    rneqd
    cbvmptv
    eqtri
    fmptd
    @81
    cG
    @0
    cS
    @1
    @18
    @2
    @33
    @17
    @2
    @4
    simprl
    adantr
    #
    @81
    cS
    vk
    @22
    @30
    cmpt
    #
    @0
    @81
    cS
    @98
    @100
    ablfac2.s
    @81
    @7
    @22
    wceq
    @31
    vk
    @7
    wral
    #
    @98
    @100
    wceq
    @92
    @81
    @101
    @32
    @95
    @81
    @31
    vk
    @7
    @22
    @92
    raleqdv
    mpbird
    vk
    @7
    @29
    @22
    @30
    mpteq12
    syl2anc
    syl5eq
    @81
    vk
    @22
    @50
    @0
    @81
    @2
    @22
    @50
    @0
    wf
    @99
    @0
    cG
    dprdf
    syl
    feqmptd
    eqtr4d
    #
    breqtrrd
    @81
    @10
    @3
    cB
    @81
    cS
    @0
    cG
    cdprd
    @102
    oveq2d
    @17
    @2
    @4
    @33
    simplrr
    eqtrd
    3jca
    jca
    ex
    eximdv
    mpd
    @12
    vw
    @13
    df-rex
    sylibr
    wph
    cB
    cC
    cG
    vs
    vr
    ablfac.b
    ablfac.c
    ablfac.1
    ablfac.2
    ablfac
    r19.29a
end
