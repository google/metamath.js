include "wor.mm"
include "coe.mm"
include "co.mm"
include "cep.mm"
include "wpo.mm"
include "ccnf.mm"
include "wfo.mm"
include "cv.mm"
include "wbr.mm"
include "cfv.mm"
include "wi.mm"
include "wral.mm"
include "wiso.mm"
include "oemapso.mm"
include "word.mm"
include "wwe.mm"
include "con0.mm"
include "wcel.mm"
include "oecl.mm"
include "syl2anc.mm"
include "eloni.mm"
include "syl.mm"
include "ordwe.mm"
include "weso.mm"
include "sopo.mm"
include "4syl.mm"
include "wf.mm"
include "crn.mm"
include "wceq.mm"
include "cantnff.mm"
include "wss.mm"
include "frn.mm"
include "onss.mm"
include "sseld.mm"
include "weq.mm"
include "eleq1.mm"
include "imbi12d.mm"
include "imbi2d.mm"
include "r19.21v.mm"
include "wa.mm"
include "wel.mm"
include "wb.mm"
include "ordelss.mm"
include "sylan.mm"
include "sselda.mm"
include "pm5.5.mm"
include "ralbidva.mm"
include "dfss3.mm"
include "syl6bbr.mm"
include "c0.mm"
include "wne.mm"
include "cop.mm"
include "crab.mm"
include "cint.mm"
include "cuni.mm"
include "comu.mm"
include "coa.mm"
include "wrex.mm"
include "cio.mm"
include "c1st.mm"
include "c2nd.mm"
include "adantr.mm"
include "simplrl.mm"
include "simplrr.mm"
include "simprl.mm"
include "onelon.mm"
include "on0eln0.mm"
include "biimpar.mm"
include "eqid.mm"
include "cantnflem4.mm"
include "csn.mm"
include "cxp.mm"
include "coi.mm"
include "cdm.mm"
include "cvv.mm"
include "cmpt2.mm"
include "cseqom.mm"
include "csupp.mm"
include "fczsupp0.mm"
include "eqcomi.mm"
include "oieq2.mm"
include "ax-mp.mm"
include "cfsupp.mm"
include "ne0i.mm"
include "ad2antrl.mm"
include "oveq1.mm"
include "neeq1d.mm"
include "syl5ibcom.mm"
include "necon2d.mm"
include "oe0m1.mm"
include "bitr3d.mm"
include "3imtr4d.mm"
include "syl5.mm"
include "imp.mm"
include "fconstmpt.mm"
include "fmptd.mm"
include "0ex.mm"
include "a1i.mm"
include "fczfsuppd.mm"
include "cantnfs.mm"
include "mpbir2and.mm"
include "cantnfval.mm"
include "cen.mm"
include "we0.mm"
include "oien.mm"
include "mp2an.mm"
include "en0.mm"
include "mpbi.mm"
include "fveq2i.mm"
include "seqom0g.mm"
include "eqtri.mm"
include "syl6eq.mm"
include "wfn.mm"
include "ffn.mm"
include "fnfvelrn.mm"
include "eqeltrrd.mm"
include "pm2.61ne.mm"
include "expr.mm"
include "sylbid.mm"
include "ex.mm"
include "com23.mm"
include "a2i.mm"
include "syl5bi.mm"
include "tfis2.mm"
include "com3l.mm"
include "mpdd.mm"
include "ssrdv.mm"
include "eqssd.mm"
include "dffo2.mm"
include "sylanbrc.mm"
include "copab.mm"
include "fveq2.mm"
include "eleq12d.mm"
include "imbi1d.mm"
include "ralbidv.mm"
include "anbi12d.mm"
include "cbvrexv.mm"
include "fveq1.mm"
include "eleq12.mm"
include "syl2an.mm"
include "eqeqan12d.mm"
include "rexbidv.mm"
include "syl5bb.mm"
include "cbvopabv.mm"
include "simprll.mm"
include "simprlr.mm"
include "simprr.mm"
include "cantnflem1.mm"
include "fvex.mm"
include "epelc.mm"
include "sylibr.mm"
include "ralrimivva.mm"
include "soisoi.mm"
include "syl22anc.mm"

theorem cantnf
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vw: setvar w
  let cA: class A
  let cB: class B
  let cS: class S
  let cT: class T
  let vc: setvar c
  let vf: setvar f
  let vg: setvar g
  let vh: setvar h
  let vk: setvar k
  let vn: setvar n
  let vt: setvar t
  let vu: setvar u
  let vv: setvar v
  let va: setvar a
  let vb: setvar b
  let vd: setvar d
  let cC: class C
  let cD: class D
  let cM: class M
  let cF: class F
  let cZ: class Z
  let cG: class G
  let cH: class H
  let cK: class K
  let cO: class O
  let cY: class Y
  let cX: class X
  assume cantnfs.s: |- S = dom ( A CNF B )
  assume cantnfs.a: |- ( ph -> A e. On )
  assume cantnfs.b: |- ( ph -> B e. On )
  assume oemapval.t: |- T = { <. x , y >. | E. z e. B ( ( x ` z ) e. ( y ` z ) /\ A. w e. B ( z e. w -> ( x ` w ) = ( y ` w ) ) ) }

  disjoint w x
  disjoint w y
  disjoint w z
  disjoint B w
  disjoint x y
  disjoint x z
  disjoint B x
  disjoint y z
  disjoint B y
  disjoint B z
  disjoint A w
  disjoint A x
  disjoint A y
  disjoint A z
  disjoint S x
  disjoint S y
  disjoint S z
  disjoint ph x
  disjoint ph y
  disjoint ph z
  disjoint c f
  disjoint c g
  disjoint c h
  disjoint c k
  disjoint c n
  disjoint c t
  disjoint c u
  disjoint c v
  disjoint c w
  disjoint c x
  disjoint c y
  disjoint c z
  disjoint B c
  disjoint f g
  disjoint f h
  disjoint f k
  disjoint f n
  disjoint f t
  disjoint f u
  disjoint f v
  disjoint f w
  disjoint f x
  disjoint f y
  disjoint f z
  disjoint B f
  disjoint g h
  disjoint g k
  disjoint g n
  disjoint g t
  disjoint g u
  disjoint g v
  disjoint g w
  disjoint g x
  disjoint g y
  disjoint g z
  disjoint B g
  disjoint h k
  disjoint h n
  disjoint h t
  disjoint h u
  disjoint h v
  disjoint h w
  disjoint h x
  disjoint h y
  disjoint h z
  disjoint B h
  disjoint k n
  disjoint k t
  disjoint k u
  disjoint k v
  disjoint k w
  disjoint k x
  disjoint k y
  disjoint k z
  disjoint B k
  disjoint n t
  disjoint n u
  disjoint n v
  disjoint n w
  disjoint n x
  disjoint n y
  disjoint n z
  disjoint B n
  disjoint t u
  disjoint t v
  disjoint t w
  disjoint t x
  disjoint t y
  disjoint t z
  disjoint B t
  disjoint u v
  disjoint u w
  disjoint u x
  disjoint u y
  disjoint u z
  disjoint B u
  disjoint v w
  disjoint v x
  disjoint v y
  disjoint v z
  disjoint B v
  disjoint a b
  disjoint a c
  disjoint a d
  disjoint a g
  disjoint a w
  disjoint a x
  disjoint a y
  disjoint a z
  disjoint C a
  disjoint b c
  disjoint b d
  disjoint b g
  disjoint b w
  disjoint b x
  disjoint b y
  disjoint b z
  disjoint C b
  disjoint c d
  disjoint C c
  disjoint d g
  disjoint d w
  disjoint d x
  disjoint d y
  disjoint d z
  disjoint C d
  disjoint C g
  disjoint C w
  disjoint C x
  disjoint C y
  disjoint C z
  disjoint D k
  disjoint D n
  disjoint D z
  disjoint a f
  disjoint a h
  disjoint a k
  disjoint a n
  disjoint a t
  disjoint a u
  disjoint a v
  disjoint A a
  disjoint b f
  disjoint b h
  disjoint b k
  disjoint b n
  disjoint b t
  disjoint b u
  disjoint b v
  disjoint A b
  disjoint A c
  disjoint d f
  disjoint d h
  disjoint d k
  disjoint d n
  disjoint d t
  disjoint d u
  disjoint d v
  disjoint A d
  disjoint A f
  disjoint A g
  disjoint A h
  disjoint A k
  disjoint A n
  disjoint A t
  disjoint A u
  disjoint A v
  disjoint M x
  disjoint M y
  disjoint T c
  disjoint T f
  disjoint T g
  disjoint T k
  disjoint T t
  disjoint T u
  disjoint T v
  disjoint F f
  disjoint F g
  disjoint F h
  disjoint F k
  disjoint F u
  disjoint F v
  disjoint F w
  disjoint F x
  disjoint F y
  disjoint F z
  disjoint S c
  disjoint S f
  disjoint S g
  disjoint S k
  disjoint S t
  disjoint S u
  disjoint S v
  disjoint Z g
  disjoint Z t
  disjoint Z x
  disjoint Z y
  disjoint Z z
  disjoint G c
  disjoint G f
  disjoint G h
  disjoint G k
  disjoint G t
  disjoint G u
  disjoint G v
  disjoint G w
  disjoint G x
  disjoint G y
  disjoint G z
  disjoint H f
  disjoint H h
  disjoint H u
  disjoint H v
  disjoint H x
  disjoint H y
  disjoint K k
  disjoint K t
  disjoint K u
  disjoint K v
  disjoint K x
  disjoint K z
  disjoint O k
  disjoint O u
  disjoint O w
  disjoint O x
  disjoint O y
  disjoint O z
  disjoint f ph
  disjoint g ph
  disjoint k ph
  disjoint n ph
  disjoint ph t
  disjoint ph u
  disjoint ph v
  disjoint Y k
  disjoint Y t
  disjoint Y w
  disjoint Y x
  disjoint Y y
  disjoint Y z
  disjoint X a
  disjoint X b
  disjoint X d
  disjoint X k
  disjoint X t
  disjoint X u
  disjoint X w
  disjoint X x
  disjoint X y
  disjoint X z
  disjoint c ph
  assert |- ( ph -> ( A CNF B ) Isom T , _E ( S , ( A ^o B ) ) )

  proof
    wph
    cS
    cT
    wor
    cA
    cB
    coe
    co
    #
    cep
    wpo
    #
    cS
    @0
    cA
    cB
    ccnf
    co
    #
    wfo
    #
    vf
    cv
    #
    vg
    cv
    #
    cT
    wbr
    #
    @4
    @2
    cfv
    #
    @5
    @2
    cfv
    #
    cep
    wbr
    #
    wi
    #
    vg
    cS
    wral
    vf
    cS
    wral
    cS
    @0
    cT
    cep
    @2
    wiso
    wph
    vx
    vy
    vz
    vw
    cA
    cB
    cS
    cT
    cantnfs.s
    cantnfs.a
    cantnfs.b
    oemapval.t
    oemapso
    wph
    @0
    word
    #
    @0
    cep
    wwe
    @0
    cep
    wor
    @1
    wph
    @0
    con0
    wcel
    #
    @11
    wph
    cA
    con0
    wcel
    #
    cB
    con0
    wcel
    #
    @12
    cantnfs.a
    cantnfs.b
    cA
    cB
    oecl
    syl2anc
    #
    @0
    eloni
    syl
    #
    @0
    ordwe
    @0
    cep
    weso
    @0
    cep
    sopo
    4syl
    wph
    cS
    @0
    @2
    wf
    #
    @2
    crn
    #
    @0
    wceq
    @3
    wph
    cA
    cB
    cS
    cantnfs.s
    cantnfs.a
    cantnfs.b
    cantnff
    #
    wph
    @18
    @0
    wph
    @17
    @18
    @0
    wss
    @19
    cS
    @0
    @2
    frn
    syl
    wph
    vt
    @0
    @18
    wph
    vt
    cv
    #
    @0
    wcel
    #
    @20
    con0
    wcel
    #
    @20
    @18
    wcel
    #
    wph
    @0
    con0
    @20
    wph
    @12
    @0
    con0
    wss
    @15
    @0
    onss
    syl
    sseld
    @22
    wph
    @21
    @23
    wph
    @21
    @23
    wi
    #
    wi
    #
    wph
    vy
    cv
    #
    @0
    wcel
    #
    @26
    @18
    wcel
    #
    wi
    #
    wi
    #
    vt
    vy
    vt
    vy
    weq
    #
    @24
    @29
    wph
    @31
    @21
    @27
    @23
    @28
    @20
    @26
    @0
    eleq1
    @20
    @26
    @18
    eleq1
    imbi12d
    imbi2d
    @30
    vy
    @20
    wral
    wph
    @29
    vy
    @20
    wral
    #
    wi
    #
    @22
    @25
    wph
    @29
    vy
    @20
    r19.21v
    @33
    @25
    wi
    @22
    wph
    @32
    @24
    wph
    @21
    @32
    @23
    wph
    @21
    @32
    @23
    wi
    wph
    @21
    wa
    #
    @32
    @20
    @18
    wss
    #
    @23
    @34
    @32
    @28
    vy
    @20
    wral
    @35
    @34
    @29
    @28
    vy
    @20
    @34
    vy
    vt
    wel
    wa
    @27
    @29
    @28
    wb
    @34
    @20
    @0
    @26
    wph
    @11
    @21
    @20
    @0
    wss
    @16
    @0
    @20
    ordelss
    sylan
    sselda
    @27
    @28
    pm5.5
    syl
    ralbidva
    vy
    @20
    @18
    dfss3
    syl6bbr
    wph
    @21
    @35
    @23
    wph
    @21
    @35
    wa
    #
    wa
    #
    @23
    c0
    @18
    wcel
    @20
    c0
    @20
    c0
    @18
    eleq1
    @37
    @20
    c0
    wne
    #
    wa
    vx
    vy
    vz
    vw
    cA
    cB
    @20
    vd
    cv
    va
    cv
    #
    vb
    cv
    #
    cop
    wceq
    cA
    @20
    cA
    vc
    cv
    #
    coe
    co
    wcel
    vc
    con0
    crab
    cint
    cuni
    #
    coe
    co
    #
    @39
    comu
    co
    @40
    coa
    co
    @20
    wceq
    wa
    vb
    @43
    wrex
    va
    con0
    wrex
    vd
    cio
    #
    cS
    cT
    @42
    @44
    c1st
    cfv
    #
    @44
    c2nd
    cfv
    #
    va
    vb
    vc
    vd
    cantnfs.s
    @37
    @13
    @38
    wph
    @13
    @36
    cantnfs.a
    adantr
    #
    adantr
    @37
    @14
    @38
    wph
    @14
    @36
    cantnfs.b
    adantr
    #
    adantr
    oemapval.t
    wph
    @21
    @35
    @38
    simplrl
    wph
    @21
    @35
    @38
    simplrr
    @37
    c0
    @20
    wcel
    #
    @38
    @37
    @22
    @49
    @38
    wb
    @37
    @12
    @21
    @22
    wph
    @12
    @36
    @15
    adantr
    wph
    @21
    @35
    simprl
    @0
    @20
    onelon
    syl2anc
    @20
    on0eln0
    syl
    biimpar
    @42
    eqid
    @44
    eqid
    @45
    eqid
    @46
    eqid
    cantnflem4
    @37
    cB
    c0
    csn
    cxp
    #
    @2
    cfv
    #
    c0
    @18
    @37
    @51
    c0
    cep
    coi
    #
    cdm
    #
    vk
    vz
    cvv
    cvv
    cA
    vk
    cv
    #
    @52
    cfv
    #
    coe
    co
    @55
    @50
    cfv
    comu
    co
    vz
    cv
    #
    coa
    co
    cmpt2
    #
    c0
    cseqom
    #
    cfv
    #
    c0
    @37
    vz
    cA
    cB
    cS
    vk
    @50
    @52
    @58
    cantnfs.s
    @47
    @48
    c0
    @50
    c0
    csupp
    co
    #
    wceq
    @52
    @60
    cep
    coi
    wceq
    @60
    c0
    cB
    c0
    fczsupp0
    eqcomi
    c0
    @60
    cep
    oieq2
    ax-mp
    @37
    @50
    cS
    wcel
    #
    cB
    cA
    @50
    wf
    #
    @50
    c0
    cfsupp
    wbr
    #
    @37
    vy
    cB
    c0
    cA
    @50
    @37
    @26
    cB
    wcel
    #
    c0
    cA
    wcel
    #
    @64
    cB
    c0
    wne
    #
    @37
    @65
    cB
    @26
    ne0i
    @37
    c0
    cB
    coe
    co
    #
    c0
    wceq
    #
    cA
    c0
    wne
    #
    @66
    @65
    @37
    cA
    c0
    @67
    c0
    @37
    @0
    c0
    wne
    #
    cA
    c0
    wceq
    #
    @67
    c0
    wne
    @21
    @70
    wph
    @35
    @0
    @20
    ne0i
    ad2antrl
    @71
    @0
    @67
    c0
    cA
    c0
    cB
    coe
    oveq1
    neeq1d
    syl5ibcom
    necon2d
    @37
    @14
    @66
    @68
    wb
    @48
    @14
    c0
    cB
    wcel
    @66
    @68
    cB
    on0eln0
    cB
    oe0m1
    bitr3d
    syl
    @37
    @13
    @65
    @69
    wb
    @47
    cA
    on0eln0
    syl
    3imtr4d
    syl5
    imp
    vy
    cB
    c0
    fconstmpt
    fmptd
    wph
    @63
    @36
    wph
    cB
    con0
    cvv
    c0
    cantnfs.b
    c0
    cvv
    wcel
    #
    wph
    0ex
    a1i
    fczfsuppd
    adantr
    wph
    @61
    @62
    @63
    wa
    wb
    @36
    wph
    cA
    cB
    cS
    @50
    cantnfs.s
    cantnfs.a
    cantnfs.b
    cantnfs
    adantr
    mpbir2and
    #
    @58
    eqid
    #
    cantnfval
    @59
    c0
    @58
    cfv
    #
    c0
    @53
    c0
    @58
    @53
    c0
    cen
    wbr
    #
    @53
    c0
    wceq
    @72
    c0
    cep
    wwe
    @76
    0ex
    cep
    we0
    c0
    cep
    @52
    cvv
    @52
    eqid
    oien
    mp2an
    @53
    en0
    mpbi
    fveq2i
    @72
    @75
    c0
    wceq
    0ex
    @57
    @58
    c0
    cvv
    @74
    seqom0g
    ax-mp
    eqtri
    syl6eq
    @37
    @2
    cS
    wfn
    #
    @61
    @51
    @18
    wcel
    @37
    @17
    @77
    wph
    @17
    @36
    @19
    adantr
    cS
    @0
    @2
    ffn
    syl
    @73
    cS
    @50
    @2
    fnfvelrn
    syl2anc
    eqeltrrd
    pm2.61ne
    expr
    sylbid
    ex
    com23
    a2i
    a1i
    syl5bi
    tfis2
    com3l
    mpdd
    ssrdv
    eqssd
    cS
    @0
    @2
    dffo2
    sylanbrc
    wph
    @10
    vf
    vg
    cS
    cS
    wph
    @4
    cS
    wcel
    #
    @5
    cS
    wcel
    #
    wa
    #
    @6
    @9
    wph
    @80
    @6
    wa
    #
    wa
    #
    @7
    @8
    wcel
    @9
    @82
    vu
    vv
    vt
    vw
    cA
    cB
    cS
    cT
    vk
    @4
    @5
    vk
    vt
    cvv
    cvv
    cA
    @54
    @5
    c0
    csupp
    co
    cep
    coi
    #
    cfv
    #
    coe
    co
    @84
    @5
    cfv
    comu
    co
    @20
    coa
    co
    cmpt2
    c0
    cseqom
    #
    @83
    @41
    @4
    cfv
    @41
    @5
    cfv
    wcel
    vc
    cB
    crab
    cuni
    #
    vc
    cantnfs.s
    wph
    @13
    @81
    cantnfs.a
    adantr
    wph
    @14
    @81
    cantnfs.b
    adantr
    cT
    @56
    vx
    cv
    #
    cfv
    #
    @56
    @26
    cfv
    #
    wcel
    #
    vz
    vw
    wel
    #
    vw
    cv
    #
    @87
    cfv
    #
    @92
    @26
    cfv
    #
    wceq
    #
    wi
    #
    vw
    cB
    wral
    #
    wa
    #
    vz
    cB
    wrex
    #
    vx
    vy
    copab
    @20
    vu
    cv
    #
    cfv
    #
    @20
    vv
    cv
    #
    cfv
    #
    wcel
    #
    vt
    vw
    wel
    #
    @92
    @100
    cfv
    #
    @92
    @102
    cfv
    #
    wceq
    #
    wi
    #
    vw
    cB
    wral
    #
    wa
    #
    vt
    cB
    wrex
    #
    vu
    vv
    copab
    oemapval.t
    @99
    @112
    vx
    vy
    vu
    vv
    @99
    @20
    @87
    cfv
    #
    @20
    @26
    cfv
    #
    wcel
    #
    @105
    @95
    wi
    #
    vw
    cB
    wral
    #
    wa
    #
    vt
    cB
    wrex
    vx
    vu
    weq
    #
    vy
    vv
    weq
    #
    wa
    #
    @112
    @98
    @118
    vz
    vt
    cB
    vz
    vt
    weq
    #
    @90
    @115
    @97
    @117
    @122
    @88
    @113
    @89
    @114
    @56
    @20
    @87
    fveq2
    @56
    @20
    @26
    fveq2
    eleq12d
    @122
    @96
    @116
    vw
    cB
    @122
    @91
    @105
    @95
    @56
    @20
    @92
    eleq1
    imbi1d
    ralbidv
    anbi12d
    cbvrexv
    @121
    @118
    @111
    vt
    cB
    @121
    @115
    @104
    @117
    @110
    @119
    @113
    @101
    wceq
    @114
    @103
    wceq
    @115
    @104
    wb
    @120
    @20
    @87
    @100
    fveq1
    @20
    @26
    @102
    fveq1
    @113
    @101
    @114
    @103
    eleq12
    syl2an
    @121
    @116
    @109
    vw
    cB
    @121
    @95
    @108
    @105
    @119
    @120
    @93
    @106
    @94
    @107
    @92
    @87
    @100
    fveq1
    @92
    @26
    @102
    fveq1
    eqeqan12d
    imbi2d
    ralbidv
    anbi12d
    rexbidv
    syl5bb
    cbvopabv
    eqtri
    wph
    @78
    @79
    @6
    simprll
    wph
    @78
    @79
    @6
    simprlr
    wph
    @80
    @6
    simprr
    @86
    eqid
    @83
    eqid
    @85
    eqid
    cantnflem1
    @7
    @8
    @5
    @2
    fvex
    epelc
    sylibr
    expr
    ralrimivva
    vf
    vg
    cS
    @0
    cT
    cep
    @2
    soisoi
    syl22anc
end
