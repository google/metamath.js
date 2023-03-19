include "wpss.mm"
include "cv.mm"
include "cin.mm"
include "csn.mm"
include "wceq.mm"
include "co.mm"
include "wa.mm"
include "csubg.mm"
include "cfv.mm"
include "wrex.mm"
include "wcel.mm"
include "wn.mm"
include "wi.mm"
include "wral.mm"
include "crab.mm"
include "ccrd.mm"
include "cdm.mm"
include "c0.mm"
include "wne.mm"
include "wss.mm"
include "crpss.mm"
include "wor.mm"
include "w3a.mm"
include "cuni.mm"
include "wal.mm"
include "cfn.mm"
include "cpw.mm"
include "pwfi.mm"
include "sylib.mm"
include "adantr.mm"
include "subgss.mm"
include "3ad2ant2.mm"
include "selpw.mm"
include "sylibr.mm"
include "rabssdv.mm"
include "ssfi.mm"
include "syl2anc.mm"
include "finnum.mm"
include "syl.mm"
include "cmre.mm"
include "cgrp.mm"
include "cacs.mm"
include "cabl.mm"
include "ablgrp.mm"
include "subgacs.mm"
include "acsmre.mm"
include "3syl.mm"
include "sseldd.mm"
include "mrcsncl.mm"
include "syl5eqel.mm"
include "simpr.mm"
include "snssd.mm"
include "sstrd.mm"
include "mrcssidd.mm"
include "syl6sseqr.mm"
include "wb.mm"
include "snssg.mm"
include "mpbird.mm"
include "psseq1.mm"
include "eleq2.mm"
include "anbi12d.mm"
include "rspcev.mm"
include "syl12anc.mm"
include "rabn0.mm"
include "simpr1.mm"
include "simpr2.mm"
include "simpr3.mm"
include "fin1a2lem10.mm"
include "syl3anc.mm"
include "ex.mm"
include "alrimiv.mm"
include "zornn0g.mm"
include "weq.mm"
include "ralrab.mm"
include "rexbii.mm"
include "r19.29.mm"
include "elrab.mm"
include "ineq2.mm"
include "eqeq1d.mm"
include "oveq2.mm"
include "cbvrexv.mm"
include "cdif.mm"
include "wex.mm"
include "simprrl.mm"
include "ad2antrr.mm"
include "psseq1d.mm"
include "pssdif.mm"
include "n0.mm"
include "cmg.mm"
include "cpgp.mm"
include "wbr.mm"
include "ad3antrrr.mm"
include "simplr.mm"
include "simprl1.mm"
include "adantrr.mm"
include "pssssd.mm"
include "simprl3.mm"
include "notbid.mm"
include "imbi2d.mm"
include "ralbidv.mm"
include "psseq2.mm"
include "imbi12d.mm"
include "cbvralv.mm"
include "syl6bb.mm"
include "simprr.mm"
include "eqid.mm"
include "pgpfac1lem4.mm"
include "expr.mm"
include "exlimdv.mm"
include "mpd.mm"
include "3exp2.mm"
include "impd.mm"
include "rexlimdva.mm"
include "syl5bi.mm"
include "sylan2b.mm"
include "syl5.mm"
include "mpand.mm"
include "syld.mm"
include "0subg.mm"
include "subg0cl.mm"
include "sseqin2.mm"
include "lsmss2.mm"
include "biimpar.mm"
include "wo.mm"
include "mrcsscl.mm"
include "syl5eqss.mm"
include "sspss.mm"
include "mpjaod.mm"

theorem pgpfac1lem5
  let wph: wff ph
  let vt: setvar t
  let cA: class A
  let cB: class B
  let cP: class P
  let c.po: class .(+)
  let cS: class S
  let cU: class U
  let cE: class E
  let cG: class G
  let cK: class K
  let cO: class O
  let c.0: class .0.
  let vs: setvar s
  let vb: setvar b
  let vk: setvar k
  let vu: setvar u
  let vv: setvar v
  let vx: setvar x
  let vy: setvar y
  let vw: setvar w
  let va: setvar a
  let vn: setvar n
  let cD: class D
  let cC: class C
  let cW: class W
  let c.x: class .x.
  assume pgpfac1.k: |- K = ( mrCls ` ( SubGrp ` G ) )
  assume pgpfac1.s: |- S = ( K ` { A } )
  assume pgpfac1.b: |- B = ( Base ` G )
  assume pgpfac1.o: |- O = ( od ` G )
  assume pgpfac1.e: |- E = ( gEx ` G )
  assume pgpfac1.z: |- .0. = ( 0g ` G )
  assume pgpfac1.l: |- .(+) = ( LSSum ` G )
  assume pgpfac1.p: |- ( ph -> P pGrp G )
  assume pgpfac1.g: |- ( ph -> G e. Abel )
  assume pgpfac1.n: |- ( ph -> B e. Fin )
  assume pgpfac1.oe: |- ( ph -> ( O ` A ) = E )
  assume pgpfac1.u: |- ( ph -> U e. ( SubGrp ` G ) )
  assume pgpfac1.au: |- ( ph -> A e. U )
  assume pgpfac1.3: |- ( ph -> A. s e. ( SubGrp ` G ) ( ( s C. U /\ A e. s ) -> E. t e. ( SubGrp ` G ) ( ( S i^i t ) = { .0. } /\ ( S .(+) t ) = s ) ) )

  disjoint s t
  disjoint .0. s
  disjoint .0. t
  disjoint A s
  disjoint A t
  disjoint .(+) s
  disjoint .(+) t
  disjoint P s
  disjoint P t
  disjoint B s
  disjoint B t
  disjoint G s
  disjoint G t
  disjoint U s
  disjoint U t
  disjoint S s
  disjoint S t
  disjoint ph s
  disjoint ph t
  disjoint K s
  disjoint K t
  disjoint b k
  disjoint b s
  disjoint b t
  disjoint b u
  disjoint b v
  disjoint b x
  disjoint b y
  disjoint .0. b
  disjoint k s
  disjoint k t
  disjoint k u
  disjoint k v
  disjoint k x
  disjoint k y
  disjoint .0. k
  disjoint s u
  disjoint s v
  disjoint s x
  disjoint s y
  disjoint t u
  disjoint t v
  disjoint t x
  disjoint t y
  disjoint u v
  disjoint u x
  disjoint u y
  disjoint .0. u
  disjoint v x
  disjoint v y
  disjoint .0. v
  disjoint x y
  disjoint .0. x
  disjoint .0. y
  disjoint b w
  disjoint A b
  disjoint k w
  disjoint A k
  disjoint s w
  disjoint t w
  disjoint u w
  disjoint A u
  disjoint v w
  disjoint A v
  disjoint w x
  disjoint w y
  disjoint A w
  disjoint A x
  disjoint A y
  disjoint a b
  disjoint a n
  disjoint a t
  disjoint a w
  disjoint a x
  disjoint a y
  disjoint D a
  disjoint b n
  disjoint D b
  disjoint n t
  disjoint n w
  disjoint n x
  disjoint n y
  disjoint D n
  disjoint D t
  disjoint D w
  disjoint D x
  disjoint D y
  disjoint a k
  disjoint a s
  disjoint a u
  disjoint a v
  disjoint .(+) a
  disjoint .(+) b
  disjoint .(+) k
  disjoint .(+) u
  disjoint .(+) v
  disjoint .(+) w
  disjoint .(+) x
  disjoint .(+) y
  disjoint E k
  disjoint O a
  disjoint P a
  disjoint P b
  disjoint P k
  disjoint P w
  disjoint P y
  disjoint B a
  disjoint k n
  disjoint B k
  disjoint n s
  disjoint n v
  disjoint B n
  disjoint B v
  disjoint G a
  disjoint G b
  disjoint G k
  disjoint n u
  disjoint G n
  disjoint G u
  disjoint G v
  disjoint G w
  disjoint G x
  disjoint G y
  disjoint U b
  disjoint U k
  disjoint U u
  disjoint U v
  disjoint U w
  disjoint U y
  disjoint C a
  disjoint C k
  disjoint C s
  disjoint C t
  disjoint C w
  disjoint S a
  disjoint S b
  disjoint S k
  disjoint S n
  disjoint S u
  disjoint S v
  disjoint S w
  disjoint S x
  disjoint S y
  disjoint W a
  disjoint W b
  disjoint W k
  disjoint W n
  disjoint W s
  disjoint W t
  disjoint W w
  disjoint W x
  disjoint W y
  disjoint a ph
  disjoint b ph
  disjoint k ph
  disjoint n ph
  disjoint ph u
  disjoint ph v
  disjoint ph w
  disjoint ph x
  disjoint ph y
  disjoint .x. a
  disjoint .x. b
  disjoint .x. k
  disjoint .x. n
  disjoint .x. s
  disjoint .x. t
  disjoint .x. w
  disjoint .x. y
  disjoint K w
  disjoint K x
  disjoint K y
  assert |- ( ph -> E. t e. ( SubGrp ` G ) ( ( S i^i t ) = { .0. } /\ ( S .(+) t ) = U ) )

  proof
    wph
    cS
    cU
    wpss
    #
    cS
    vt
    cv
    #
    cin
    #
    c.0
    csn
    #
    wceq
    #
    cS
    @1
    c.po
    co
    #
    cU
    wceq
    #
    wa
    #
    vt
    cG
    csubg
    cfv
    #
    wrex
    #
    cS
    cU
    wceq
    #
    wph
    @0
    vw
    cv
    #
    cU
    wpss
    #
    cA
    @11
    wcel
    #
    wa
    #
    vs
    cv
    #
    @11
    wpss
    #
    wn
    #
    wi
    #
    vw
    @8
    wral
    #
    vs
    vv
    cv
    #
    cU
    wpss
    #
    cA
    @20
    wcel
    #
    wa
    #
    vv
    @8
    crab
    #
    wrex
    #
    @9
    wph
    @0
    @25
    wph
    @0
    wa
    #
    @17
    vw
    @24
    wral
    #
    vs
    @24
    wrex
    #
    @25
    @26
    @24
    ccrd
    cdm
    wcel
    #
    @24
    c0
    wne
    #
    vu
    cv
    #
    @24
    wss
    #
    @31
    c0
    wne
    #
    @31
    crpss
    wor
    #
    w3a
    #
    @31
    cuni
    #
    @24
    wcel
    #
    wi
    #
    vu
    wal
    @28
    @26
    @24
    cfn
    wcel
    #
    @29
    @26
    cB
    cpw
    #
    cfn
    wcel
    #
    @24
    @40
    wss
    @39
    wph
    @41
    @0
    wph
    cB
    cfn
    wcel
    #
    @41
    pgpfac1.n
    cB
    pwfi
    sylib
    adantr
    @26
    @23
    vv
    @8
    @40
    @26
    @20
    @8
    wcel
    #
    @23
    w3a
    @20
    cB
    wss
    #
    @20
    @40
    wcel
    @43
    @26
    @44
    @23
    cB
    @20
    cG
    pgpfac1.b
    subgss
    3ad2ant2
    vv
    cB
    selpw
    sylibr
    rabssdv
    @40
    @24
    ssfi
    syl2anc
    #
    @24
    finnum
    syl
    @26
    @23
    vv
    @8
    wrex
    #
    @30
    @26
    cS
    @8
    wcel
    #
    @0
    cA
    cS
    wcel
    #
    @46
    wph
    @47
    @0
    wph
    cS
    cA
    csn
    #
    cK
    cfv
    #
    @8
    pgpfac1.s
    wph
    @8
    cB
    cmre
    cfv
    wcel
    #
    cA
    cB
    wcel
    #
    @50
    @8
    wcel
    wph
    cG
    cgrp
    wcel
    #
    @8
    cB
    cacs
    cfv
    wcel
    @51
    wph
    cG
    cabl
    wcel
    #
    @53
    pgpfac1.g
    cG
    ablgrp
    syl
    #
    cB
    cG
    pgpfac1.b
    subgacs
    @8
    cB
    acsmre
    3syl
    #
    wph
    cU
    cB
    cA
    wph
    cU
    @8
    wcel
    #
    cU
    cB
    wss
    pgpfac1.u
    cB
    cU
    cG
    pgpfac1.b
    subgss
    syl
    #
    pgpfac1.au
    sseldd
    #
    @8
    cA
    cK
    cB
    pgpfac1.k
    mrcsncl
    syl2anc
    syl5eqel
    #
    adantr
    wph
    @0
    simpr
    wph
    @48
    @0
    wph
    @48
    @49
    cS
    wss
    #
    wph
    @49
    @50
    cS
    wph
    @8
    @49
    cK
    cB
    @56
    pgpfac1.k
    wph
    @49
    cU
    cB
    wph
    cA
    cU
    pgpfac1.au
    snssd
    #
    @58
    sstrd
    mrcssidd
    pgpfac1.s
    syl6sseqr
    wph
    @52
    @48
    @61
    wb
    @59
    cA
    cS
    cB
    snssg
    syl
    mpbird
    adantr
    @23
    @0
    @48
    wa
    vv
    cS
    @8
    @20
    cS
    wceq
    @21
    @0
    @22
    @48
    @20
    cS
    cU
    psseq1
    @20
    cS
    cA
    eleq2
    anbi12d
    rspcev
    syl12anc
    @23
    vv
    @8
    rabn0
    sylibr
    @26
    @38
    vu
    @26
    @35
    @37
    @26
    @35
    wa
    #
    @31
    @24
    @36
    @26
    @32
    @33
    @34
    simpr1
    #
    @63
    @33
    @31
    cfn
    wcel
    #
    @34
    @36
    @31
    wcel
    @26
    @32
    @33
    @34
    simpr2
    @63
    @39
    @32
    @65
    @26
    @39
    @35
    @45
    adantr
    @64
    @24
    @31
    ssfi
    syl2anc
    @26
    @32
    @33
    @34
    simpr3
    @31
    fin1a2lem10
    syl3anc
    sseldd
    ex
    alrimiv
    vs
    vw
    vu
    @24
    zornn0g
    syl3anc
    @27
    @19
    vs
    @24
    @23
    @14
    @17
    vw
    vv
    @8
    vv
    vw
    weq
    @21
    @12
    @22
    @13
    @20
    @11
    cU
    psseq1
    @20
    @11
    cA
    eleq2
    anbi12d
    ralrab
    rexbii
    sylib
    ex
    wph
    @4
    @5
    @15
    wceq
    #
    wa
    #
    vt
    @8
    wrex
    #
    vs
    @24
    wral
    #
    @25
    @9
    wph
    @15
    cU
    wpss
    #
    cA
    @15
    wcel
    #
    wa
    #
    @68
    wi
    vs
    @8
    wral
    @69
    pgpfac1.3
    @23
    @72
    @68
    vs
    vv
    @8
    vv
    vs
    weq
    @21
    @70
    @22
    @71
    @20
    @15
    cU
    psseq1
    @20
    @15
    cA
    eleq2
    anbi12d
    #
    ralrab
    sylibr
    @69
    @25
    wa
    @68
    @19
    wa
    #
    vs
    @24
    wrex
    wph
    @9
    @68
    @19
    vs
    @24
    r19.29
    wph
    @74
    @9
    vs
    @24
    @15
    @24
    wcel
    wph
    @15
    @8
    wcel
    #
    @72
    wa
    #
    @74
    @9
    wi
    @23
    @72
    vv
    @15
    @8
    @73
    elrab
    wph
    @76
    wa
    #
    @68
    @19
    @9
    @68
    cS
    @20
    cin
    #
    @3
    wceq
    #
    cS
    @20
    c.po
    co
    #
    @15
    wceq
    #
    wa
    #
    vv
    @8
    wrex
    @77
    @19
    @9
    wi
    #
    @67
    @82
    vt
    vv
    @8
    vt
    vv
    weq
    #
    @4
    @79
    @66
    @81
    @84
    @2
    @78
    @3
    @1
    @20
    cS
    ineq2
    eqeq1d
    @84
    @5
    @80
    @15
    @1
    @20
    cS
    c.po
    oveq2
    eqeq1d
    anbi12d
    cbvrexv
    @77
    @82
    @83
    vv
    @8
    @77
    @43
    wa
    #
    @79
    @81
    @83
    @85
    @79
    @81
    @19
    @9
    @85
    @79
    @81
    @19
    w3a
    #
    wa
    #
    vb
    cv
    #
    cU
    @80
    cdif
    #
    wcel
    #
    vb
    wex
    #
    @9
    @87
    @80
    cU
    wpss
    #
    @91
    @87
    @92
    @70
    @77
    @70
    @43
    @86
    wph
    @75
    @70
    @71
    simprrl
    ad2antrr
    @87
    @80
    @15
    cU
    @85
    @79
    @81
    @19
    simpr2
    #
    psseq1d
    mpbird
    #
    @92
    @89
    c0
    wne
    @91
    @80
    cU
    pssdif
    vb
    @89
    n0
    sylib
    syl
    @87
    @90
    @9
    vb
    @85
    @86
    @90
    @9
    @85
    @86
    @90
    wa
    #
    wa
    #
    vy
    vt
    cA
    cB
    @88
    cP
    c.po
    cS
    cG
    cmg
    cfv
    #
    cU
    cE
    cG
    cK
    cO
    @20
    c.0
    pgpfac1.k
    pgpfac1.s
    pgpfac1.b
    pgpfac1.o
    pgpfac1.e
    pgpfac1.z
    pgpfac1.l
    wph
    cP
    cG
    cpgp
    wbr
    @76
    @43
    @95
    pgpfac1.p
    ad3antrrr
    wph
    @54
    @76
    @43
    @95
    pgpfac1.g
    ad3antrrr
    wph
    @42
    @76
    @43
    @95
    pgpfac1.n
    ad3antrrr
    wph
    cA
    cO
    cfv
    cE
    wceq
    @76
    @43
    @95
    pgpfac1.oe
    ad3antrrr
    wph
    @57
    @76
    @43
    @95
    pgpfac1.u
    ad3antrrr
    wph
    cA
    cU
    wcel
    @76
    @43
    @95
    pgpfac1.au
    ad3antrrr
    @77
    @43
    @95
    simplr
    @79
    @81
    @19
    @90
    @85
    simprl1
    @96
    @80
    cU
    @85
    @86
    @92
    @90
    @94
    adantrr
    pssssd
    @96
    vy
    cv
    #
    cU
    wpss
    #
    cA
    @98
    wcel
    #
    wa
    #
    @80
    @98
    wpss
    #
    wn
    #
    wi
    #
    vy
    @8
    wral
    #
    @19
    @79
    @81
    @19
    @90
    @85
    simprl3
    @96
    @81
    @105
    @19
    wb
    @85
    @86
    @81
    @90
    @93
    adantrr
    @81
    @105
    @101
    @15
    @98
    wpss
    #
    wn
    #
    wi
    #
    vy
    @8
    wral
    @19
    @81
    @104
    @108
    vy
    @8
    @81
    @103
    @107
    @101
    @81
    @102
    @106
    @80
    @15
    @98
    psseq1
    notbid
    imbi2d
    ralbidv
    @108
    @18
    vy
    vw
    @8
    vy
    vw
    weq
    #
    @101
    @14
    @107
    @17
    @109
    @99
    @12
    @100
    @13
    @98
    @11
    cU
    psseq1
    @98
    @11
    cA
    eleq2
    anbi12d
    @109
    @106
    @16
    @98
    @11
    @15
    psseq2
    notbid
    imbi12d
    cbvralv
    syl6bb
    syl
    mpbird
    @85
    @86
    @90
    simprr
    @97
    eqid
    pgpfac1lem4
    expr
    exlimdv
    mpd
    3exp2
    impd
    rexlimdva
    syl5bi
    impd
    sylan2b
    rexlimdva
    syl5
    mpand
    syld
    wph
    @10
    @9
    wph
    @10
    wa
    #
    @3
    @8
    wcel
    #
    cS
    @3
    cin
    #
    @3
    wceq
    #
    cS
    @3
    c.po
    co
    #
    cU
    wceq
    #
    @9
    wph
    @111
    @10
    wph
    @53
    @111
    @55
    cG
    c.0
    pgpfac1.z
    0subg
    syl
    #
    adantr
    @110
    @3
    cS
    wss
    #
    @113
    wph
    @117
    @10
    wph
    c.0
    cS
    wph
    @47
    c.0
    cS
    wcel
    @60
    cS
    cG
    c.0
    pgpfac1.z
    subg0cl
    syl
    snssd
    #
    adantr
    @3
    cS
    sseqin2
    sylib
    wph
    @115
    @10
    wph
    @114
    cS
    cU
    wph
    @47
    @111
    @117
    @114
    cS
    wceq
    @60
    @116
    @118
    c.po
    cS
    @3
    cG
    pgpfac1.l
    lsmss2
    syl3anc
    eqeq1d
    biimpar
    @7
    @113
    @115
    wa
    vt
    @3
    @8
    @1
    @3
    wceq
    #
    @4
    @113
    @6
    @115
    @119
    @2
    @112
    @3
    @1
    @3
    cS
    ineq2
    eqeq1d
    @119
    @5
    @114
    cU
    @1
    @3
    cS
    c.po
    oveq2
    eqeq1d
    anbi12d
    rspcev
    syl12anc
    ex
    wph
    cS
    cU
    wss
    @0
    @10
    wo
    wph
    cS
    @50
    cU
    pgpfac1.s
    wph
    @51
    @49
    cU
    wss
    @57
    @50
    cU
    wss
    @56
    @62
    pgpfac1.u
    @8
    @49
    cK
    cU
    cB
    pgpfac1.k
    mrcsscl
    syl3anc
    syl5eqss
    cS
    cU
    sspss
    sylib
    mpjaod
end
