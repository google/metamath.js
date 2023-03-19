include "c0.mm"
include "wceq.mm"
include "cfv.mm"
include "coe.mm"
include "co.mm"
include "wcel.mm"
include "cv.mm"
include "csuc.mm"
include "com.mm"
include "wrex.mm"
include "con0.mm"
include "oen0.mm"
include "syl21anc.mm"
include "fveq2.mm"
include "cvv.mm"
include "0ex.mm"
include "comu.mm"
include "coa.mm"
include "cmpt2.mm"
include "seqom0g.mm"
include "ax-mp.mm"
include "syl6eq.mm"
include "eleq1d.mm"
include "syl5ibrcom.mm"
include "wa.mm"
include "wss.mm"
include "word.mm"
include "adantr.mm"
include "eloni.mm"
include "syl.mm"
include "cima.mm"
include "cdm.mm"
include "wfn.mm"
include "csupp.mm"
include "wf.mm"
include "cep.mm"
include "oif.mm"
include "ffn.mm"
include "mp1i.mm"
include "wb.mm"
include "oicl.mm"
include "ordsuc.mm"
include "mpbi.mm"
include "ordelon.mm"
include "sylancr.mm"
include "ordsssuc.mm"
include "sylancl.mm"
include "mpbird.mm"
include "vex.mm"
include "sucid.mm"
include "simprr.mm"
include "syl5eleqr.mm"
include "fnfvima.mm"
include "syl3anc.mm"
include "sseldd.mm"
include "ordsucss.mm"
include "sylc.mm"
include "wi.mm"
include "suppssdm.mm"
include "cfsupp.mm"
include "wbr.mm"
include "cantnfs.mm"
include "mpbid.mm"
include "simpld.mm"
include "fdm.mm"
include "syl5sseq.mm"
include "onss.mm"
include "sstrd.mm"
include "eqeltrrd.mm"
include "ordsucelsuc.mm"
include "sylibr.mm"
include "ffvelrni.mm"
include "suceloni.mm"
include "oewordi.mm"
include "syl31anc.mm"
include "mpd.mm"
include "fveq2d.mm"
include "simprl.mm"
include "simpl.mm"
include "eleq1.mm"
include "suceq.mm"
include "oveq2d.mm"
include "eleq12d.mm"
include "imbi12d.mm"
include "sselda.mm"
include "sylan2.mm"
include "ffvelrnd.mm"
include "onelon.mm"
include "syl2anc.mm"
include "oecl.mm"
include "omord2.mm"
include "peano1.mm"
include "a1i.mm"
include "cantnfsuc.mm"
include "oveq2i.mm"
include "omcl.mm"
include "oa0.mm"
include "syl5eq.mm"
include "eqtrd.mm"
include "oesuc.mm"
include "3eltr4d.mm"
include "ex.mm"
include "wtr.mm"
include "ordtr.mm"
include "trsuc.mm"
include "mpan.mm"
include "imim1i.mm"
include "ad2antrr.mm"
include "ad2antrl.mm"
include "omwordi.mm"
include "sseqtr4d.mm"
include "sucex.mm"
include "epelc.mm"
include "mpbir.mm"
include "wiso.mm"
include "wwe.mm"
include "ssexd.mm"
include "cantnfcl.mm"
include "oiiso.mm"
include "isorel.mm"
include "syl12anc.mm"
include "mpbii.mm"
include "fvex.mm"
include "sylib.mm"
include "peano2.mm"
include "ad2antlr.mm"
include "cantnfvalf.mm"
include "oaord.mm"
include "omsuc.mm"
include "exp32.mm"
include "a2d.mm"
include "syl5.mm"
include "expcom.mm"
include "finds2.mm"
include "syl3c.mm"
include "eqeltrd.mm"
include "rexlimdvaa.mm"
include "wo.mm"
include "simprd.mm"
include "elnn.mm"
include "nn0suc.mm"
include "mpjaod.mm"

theorem cantnflt
  let wph: wff ph
  let vz: setvar z
  let cA: class A
  let cB: class B
  let cC: class C
  let cS: class S
  let vk: setvar k
  let cF: class F
  let cG: class G
  let cH: class H
  let cK: class K
  let vc: setvar c
  let vf: setvar f
  let vg: setvar g
  let vh: setvar h
  let vn: setvar n
  let vt: setvar t
  let vu: setvar u
  let vv: setvar v
  let vw: setvar w
  let vx: setvar x
  let vy: setvar y
  let va: setvar a
  let vb: setvar b
  let vd: setvar d
  let cD: class D
  let cM: class M
  let cT: class T
  let cZ: class Z
  let cO: class O
  let cY: class Y
  let cX: class X
  assume cantnfs.s: |- S = dom ( A CNF B )
  assume cantnfs.a: |- ( ph -> A e. On )
  assume cantnfs.b: |- ( ph -> B e. On )
  assume cantnfcl.g: |- G = OrdIso ( _E , ( F supp (/) ) )
  assume cantnfcl.f: |- ( ph -> F e. S )
  assume cantnfval.h: |- H = seqom ( ( k e. _V , z e. _V |-> ( ( ( A ^o ( G ` k ) ) .o ( F ` ( G ` k ) ) ) +o z ) ) , (/) )
  assume cantnflt.a: |- ( ph -> (/) e. A )
  assume cantnflt.k: |- ( ph -> K e. suc dom G )
  assume cantnflt.c: |- ( ph -> C e. On )
  assume cantnflt.s: |- ( ph -> ( G " K ) C_ C )

  disjoint k z
  disjoint B k
  disjoint B z
  disjoint C z
  disjoint A k
  disjoint A z
  disjoint F k
  disjoint F z
  disjoint S k
  disjoint S z
  disjoint G k
  disjoint G z
  disjoint K k
  disjoint K z
  disjoint k ph
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
  disjoint w x
  disjoint w y
  disjoint w z
  disjoint B w
  disjoint x y
  disjoint x z
  disjoint B x
  disjoint y z
  disjoint B y
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
  disjoint A n
  disjoint A t
  disjoint A u
  disjoint A v
  disjoint A w
  disjoint A x
  disjoint A y
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
  disjoint F u
  disjoint F v
  disjoint F w
  disjoint F x
  disjoint F y
  disjoint S c
  disjoint S f
  disjoint S g
  disjoint S t
  disjoint S u
  disjoint S v
  disjoint S x
  disjoint S y
  disjoint Z g
  disjoint Z t
  disjoint Z x
  disjoint Z y
  disjoint Z z
  disjoint G c
  disjoint G f
  disjoint G h
  disjoint G t
  disjoint G u
  disjoint G v
  disjoint G w
  disjoint G x
  disjoint G y
  disjoint H f
  disjoint H h
  disjoint H u
  disjoint H v
  disjoint H x
  disjoint H y
  disjoint K t
  disjoint K u
  disjoint K v
  disjoint K x
  disjoint O k
  disjoint O u
  disjoint O w
  disjoint O x
  disjoint O y
  disjoint O z
  disjoint f ph
  disjoint g ph
  disjoint n ph
  disjoint ph t
  disjoint ph u
  disjoint ph v
  disjoint ph x
  disjoint ph y
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
  assert |- ( ph -> ( H ` K ) e. ( A ^o C ) )

  proof
    wph
    cK
    c0
    wceq
    #
    cK
    cH
    cfv
    #
    cA
    cC
    coe
    co
    #
    wcel
    #
    cK
    vx
    cv
    #
    csuc
    #
    wceq
    #
    vx
    com
    wrex
    #
    wph
    @3
    @0
    c0
    @2
    wcel
    #
    wph
    cA
    con0
    wcel
    #
    cC
    con0
    wcel
    #
    c0
    cA
    wcel
    #
    @8
    cantnfs.a
    cantnflt.c
    cantnflt.a
    cA
    cC
    oen0
    syl21anc
    @0
    @1
    c0
    @2
    @0
    @1
    c0
    cH
    cfv
    #
    c0
    cK
    c0
    cH
    fveq2
    c0
    cvv
    wcel
    @12
    c0
    wceq
    0ex
    vk
    vz
    cvv
    cvv
    cA
    vk
    cv
    cG
    cfv
    #
    coe
    co
    @13
    cF
    cfv
    comu
    co
    #
    vz
    cv
    #
    coa
    co
    cmpt2
    cH
    c0
    cvv
    cantnfval.h
    seqom0g
    ax-mp
    #
    syl6eq
    eleq1d
    syl5ibrcom
    wph
    @6
    @3
    vx
    com
    wph
    @4
    com
    wcel
    #
    @6
    wa
    #
    wa
    #
    cA
    @4
    cG
    cfv
    #
    csuc
    #
    coe
    co
    #
    @2
    @1
    @19
    @21
    cC
    wss
    #
    @22
    @2
    wss
    #
    @19
    cC
    word
    #
    @20
    cC
    wcel
    @23
    @19
    @10
    @25
    wph
    @10
    @18
    cantnflt.c
    adantr
    #
    cC
    eloni
    syl
    @19
    cG
    cK
    cima
    #
    cC
    @20
    wph
    @27
    cC
    wss
    @18
    cantnflt.s
    adantr
    @19
    cG
    cG
    cdm
    #
    wfn
    #
    cK
    @28
    wss
    #
    @4
    cK
    wcel
    @20
    @27
    wcel
    @28
    cF
    c0
    csupp
    co
    #
    cG
    wf
    @29
    @19
    @31
    cep
    cG
    cantnfcl.g
    oif
    #
    @28
    @31
    cG
    ffn
    mp1i
    wph
    @30
    @18
    wph
    @30
    cK
    @28
    csuc
    #
    wcel
    #
    cantnflt.k
    wph
    cK
    con0
    wcel
    #
    @28
    word
    #
    @30
    @34
    wb
    wph
    @33
    word
    #
    @34
    @35
    @36
    @37
    @31
    cep
    cG
    cantnfcl.g
    oicl
    #
    @28
    ordsuc
    mpbi
    cantnflt.k
    @33
    cK
    ordelon
    sylancr
    @38
    cK
    @28
    ordsssuc
    sylancl
    mpbird
    adantr
    @19
    @4
    @5
    cK
    @4
    vx
    vex
    sucid
    wph
    @17
    @6
    simprr
    #
    syl5eleqr
    @28
    cK
    cG
    @4
    fnfvima
    syl3anc
    sseldd
    @20
    cC
    ordsucss
    sylc
    @19
    @21
    con0
    wcel
    #
    @10
    @9
    @11
    @23
    @24
    wi
    @19
    @20
    con0
    wcel
    @40
    @19
    @31
    con0
    @20
    wph
    @31
    con0
    wss
    #
    @18
    wph
    @31
    cB
    con0
    wph
    cF
    cdm
    #
    @31
    cB
    cF
    c0
    suppssdm
    wph
    cB
    cA
    cF
    wf
    #
    @42
    cB
    wceq
    wph
    @43
    cF
    c0
    cfsupp
    wbr
    #
    wph
    cF
    cS
    wcel
    @43
    @44
    wa
    cantnfcl.f
    wph
    cA
    cB
    cS
    cF
    cantnfs.s
    cantnfs.a
    cantnfs.b
    cantnfs
    mpbid
    simpld
    #
    cB
    cA
    cF
    fdm
    syl
    syl5sseq
    #
    wph
    cB
    con0
    wcel
    cB
    con0
    wss
    cantnfs.b
    cB
    onss
    syl
    sstrd
    #
    adantr
    @19
    @4
    @28
    wcel
    #
    @20
    @31
    wcel
    @19
    @5
    @33
    wcel
    #
    @48
    @19
    cK
    @5
    @33
    @39
    wph
    @34
    @18
    cantnflt.k
    adantr
    eqeltrrd
    @36
    @48
    @49
    wb
    @38
    @4
    @28
    ordsucelsuc
    ax-mp
    sylibr
    #
    @28
    @31
    @4
    cG
    @32
    ffvelrni
    syl
    sseldd
    @20
    suceloni
    syl
    @26
    wph
    @9
    @18
    cantnfs.a
    adantr
    wph
    @11
    @18
    cantnflt.a
    adantr
    @21
    cC
    cA
    oewordi
    syl31anc
    mpd
    @19
    @1
    @5
    cH
    cfv
    #
    @22
    @19
    cK
    @5
    cH
    @39
    fveq2d
    @19
    @17
    wph
    @48
    @51
    @22
    wcel
    #
    wph
    @17
    @6
    simprl
    wph
    @18
    simpl
    @50
    @48
    @52
    wi
    c0
    @28
    wcel
    #
    c0
    csuc
    #
    cH
    cfv
    #
    cA
    c0
    cG
    cfv
    #
    csuc
    #
    coe
    co
    #
    wcel
    #
    wi
    vy
    cv
    #
    @28
    wcel
    #
    @60
    csuc
    #
    cH
    cfv
    #
    cA
    @60
    cG
    cfv
    #
    csuc
    #
    coe
    co
    #
    wcel
    #
    wi
    #
    @62
    @28
    wcel
    #
    @62
    csuc
    #
    cH
    cfv
    #
    cA
    @62
    cG
    cfv
    #
    csuc
    #
    coe
    co
    #
    wcel
    #
    wi
    #
    wph
    vx
    vy
    @4
    c0
    wceq
    #
    @48
    @53
    @52
    @59
    @4
    c0
    @28
    eleq1
    @77
    @51
    @55
    @22
    @58
    @77
    @5
    @54
    cH
    @4
    c0
    suceq
    fveq2d
    @77
    @21
    @57
    cA
    coe
    @77
    @20
    @56
    wceq
    @21
    @57
    wceq
    @4
    c0
    cG
    fveq2
    @20
    @56
    suceq
    syl
    oveq2d
    eleq12d
    imbi12d
    @4
    @60
    wceq
    #
    @48
    @61
    @52
    @67
    @4
    @60
    @28
    eleq1
    @78
    @51
    @63
    @22
    @66
    @78
    @5
    @62
    cH
    @4
    @60
    suceq
    fveq2d
    @78
    @21
    @65
    cA
    coe
    @78
    @20
    @64
    wceq
    @21
    @65
    wceq
    @4
    @60
    cG
    fveq2
    @20
    @64
    suceq
    syl
    oveq2d
    eleq12d
    imbi12d
    @4
    @62
    wceq
    #
    @48
    @69
    @52
    @75
    @4
    @62
    @28
    eleq1
    @79
    @51
    @71
    @22
    @74
    @79
    @5
    @70
    cH
    @4
    @62
    suceq
    fveq2d
    @79
    @21
    @73
    cA
    coe
    @79
    @20
    @72
    wceq
    @21
    @73
    wceq
    @4
    @62
    cG
    fveq2
    @20
    @72
    suceq
    syl
    oveq2d
    eleq12d
    imbi12d
    wph
    @53
    @59
    wph
    @53
    wa
    #
    cA
    @56
    coe
    co
    #
    @56
    cF
    cfv
    #
    comu
    co
    #
    @81
    cA
    comu
    co
    #
    @55
    @58
    @80
    @82
    cA
    wcel
    #
    @83
    @84
    wcel
    #
    @80
    cB
    cA
    @56
    cF
    wph
    @43
    @53
    @45
    adantr
    @53
    wph
    @56
    @31
    wcel
    #
    @56
    cB
    wcel
    @28
    @31
    c0
    cG
    @32
    ffvelrni
    #
    wph
    @31
    cB
    @56
    @46
    sselda
    sylan2
    ffvelrnd
    #
    @80
    @82
    con0
    wcel
    #
    @9
    @81
    con0
    wcel
    #
    c0
    @81
    wcel
    #
    @85
    @86
    wb
    @80
    @9
    @85
    @90
    wph
    @9
    @53
    cantnfs.a
    adantr
    #
    @89
    cA
    @82
    onelon
    syl2anc
    #
    @93
    @80
    @9
    @56
    con0
    wcel
    #
    @91
    @93
    @53
    wph
    @87
    @95
    @88
    wph
    @31
    con0
    @56
    @47
    sselda
    sylan2
    #
    cA
    @56
    oecl
    syl2anc
    #
    @80
    @9
    @95
    @11
    @92
    @93
    @96
    wph
    @11
    @53
    cantnflt.a
    adantr
    cA
    @56
    oen0
    syl21anc
    @82
    cA
    @81
    omord2
    syl31anc
    mpbid
    @80
    @55
    @83
    @12
    coa
    co
    #
    @83
    @53
    wph
    c0
    com
    wcel
    #
    @55
    @98
    wceq
    @99
    @53
    peano1
    a1i
    wph
    vz
    cA
    cB
    cS
    vk
    cF
    cG
    cH
    c0
    cantnfs.s
    cantnfs.a
    cantnfs.b
    cantnfcl.g
    cantnfcl.f
    cantnfval.h
    cantnfsuc
    sylan2
    @80
    @98
    @83
    c0
    coa
    co
    #
    @83
    @12
    c0
    @83
    coa
    @16
    oveq2i
    @80
    @83
    con0
    wcel
    #
    @100
    @83
    wceq
    @80
    @91
    @90
    @101
    @97
    @94
    @81
    @82
    omcl
    syl2anc
    @83
    oa0
    syl
    syl5eq
    eqtrd
    @80
    @9
    @95
    @58
    @84
    wceq
    @93
    @96
    cA
    @56
    oesuc
    syl2anc
    3eltr4d
    ex
    wph
    @60
    com
    wcel
    #
    @68
    @76
    wi
    @68
    @69
    @67
    wi
    wph
    @102
    wa
    #
    @76
    @69
    @61
    @67
    @28
    wtr
    #
    @69
    @61
    @36
    @104
    @38
    @28
    ordtr
    ax-mp
    @28
    @60
    trsuc
    mpan
    #
    imim1i
    @103
    @69
    @67
    @75
    @103
    @69
    @67
    @75
    @103
    @69
    @67
    wa
    #
    wa
    #
    cA
    @72
    coe
    co
    #
    @72
    cF
    cfv
    #
    csuc
    #
    comu
    co
    #
    @74
    @71
    @107
    @111
    @108
    cA
    comu
    co
    #
    @74
    @107
    @110
    cA
    wss
    #
    @111
    @112
    wss
    #
    @107
    cA
    word
    #
    @109
    cA
    wcel
    #
    @113
    @107
    @9
    @115
    wph
    @9
    @102
    @106
    cantnfs.a
    ad2antrr
    #
    cA
    eloni
    syl
    @107
    cB
    cA
    @72
    cF
    wph
    @43
    @102
    @106
    @45
    ad2antrr
    @107
    @31
    cB
    @72
    wph
    @31
    cB
    wss
    @102
    @106
    @46
    ad2antrr
    @69
    @72
    @31
    wcel
    @103
    @67
    @28
    @31
    @62
    cG
    @32
    ffvelrni
    ad2antrl
    #
    sseldd
    ffvelrnd
    #
    @109
    cA
    ordsucss
    sylc
    @107
    @110
    con0
    wcel
    #
    @9
    @108
    con0
    wcel
    #
    @113
    @114
    wi
    @107
    @109
    con0
    wcel
    #
    @120
    @107
    @9
    @116
    @122
    @117
    @119
    cA
    @109
    onelon
    syl2anc
    #
    @109
    suceloni
    syl
    @117
    @107
    @9
    @72
    con0
    wcel
    #
    @121
    @117
    @107
    @31
    con0
    @72
    wph
    @41
    @102
    @106
    @47
    ad2antrr
    #
    @118
    sseldd
    #
    cA
    @72
    oecl
    syl2anc
    #
    @110
    cA
    @108
    omwordi
    syl3anc
    mpd
    @107
    @9
    @124
    @74
    @112
    wceq
    @117
    @126
    cA
    @72
    oesuc
    syl2anc
    sseqtr4d
    @107
    @108
    @109
    comu
    co
    #
    @63
    coa
    co
    #
    @128
    @108
    coa
    co
    #
    @71
    @111
    @107
    @63
    @108
    wcel
    #
    @129
    @130
    wcel
    #
    @107
    @66
    @108
    @63
    @107
    @65
    @72
    wss
    #
    @66
    @108
    wss
    #
    @107
    @72
    word
    #
    @64
    @72
    wcel
    #
    @133
    @107
    @124
    @135
    @126
    @72
    eloni
    syl
    @107
    @64
    @72
    cep
    wbr
    #
    @136
    @107
    @60
    @62
    cep
    wbr
    #
    @137
    @138
    @60
    @62
    wcel
    @60
    vy
    vex
    #
    sucid
    @60
    @62
    @60
    @139
    sucex
    epelc
    mpbir
    @107
    @28
    @31
    cep
    cep
    cG
    wiso
    #
    @61
    @69
    @138
    @137
    wb
    wph
    @140
    @102
    @106
    wph
    @31
    cvv
    wcel
    @31
    cep
    wwe
    #
    @140
    wph
    @31
    cB
    con0
    cantnfs.b
    @46
    ssexd
    wph
    @141
    @28
    com
    wcel
    #
    wph
    cA
    cB
    cS
    cF
    cG
    cantnfs.s
    cantnfs.a
    cantnfs.b
    cantnfcl.g
    cantnfcl.f
    cantnfcl
    #
    simpld
    @31
    cep
    cG
    cvv
    cantnfcl.g
    oiiso
    syl2anc
    ad2antrr
    @69
    @61
    @103
    @67
    @105
    ad2antrl
    #
    @103
    @69
    @67
    simprl
    @28
    @31
    @60
    @62
    cep
    cep
    cG
    isorel
    syl12anc
    mpbii
    @64
    @72
    @62
    cG
    fvex
    epelc
    sylib
    @64
    @72
    ordsucss
    sylc
    @107
    @65
    con0
    wcel
    #
    @124
    @9
    @11
    @133
    @134
    wi
    @107
    @64
    con0
    wcel
    @145
    @107
    @31
    con0
    @64
    @125
    @107
    @61
    @64
    @31
    wcel
    @144
    @28
    @31
    @60
    cG
    @32
    ffvelrni
    syl
    sseldd
    @64
    suceloni
    syl
    @126
    @117
    wph
    @11
    @102
    @106
    cantnflt.a
    ad2antrr
    @65
    @72
    cA
    oewordi
    syl31anc
    mpd
    @103
    @69
    @67
    simprr
    sseldd
    @107
    @63
    con0
    wcel
    #
    @121
    @128
    con0
    wcel
    #
    @131
    @132
    wb
    @107
    @62
    com
    wcel
    #
    @146
    @102
    @148
    wph
    @106
    @60
    peano2
    #
    ad2antlr
    com
    con0
    @62
    cH
    vz
    cvv
    cvv
    @14
    @15
    vk
    cH
    cantnfval.h
    cantnfvalf
    ffvelrni
    syl
    @127
    @107
    @121
    @122
    @147
    @127
    @123
    @108
    @109
    omcl
    syl2anc
    @63
    @108
    @128
    oaord
    syl3anc
    mpbid
    @103
    @71
    @129
    wceq
    #
    @106
    @102
    wph
    @148
    @150
    @149
    wph
    vz
    cA
    cB
    cS
    vk
    cF
    cG
    cH
    @62
    cantnfs.s
    cantnfs.a
    cantnfs.b
    cantnfcl.g
    cantnfcl.f
    cantnfval.h
    cantnfsuc
    sylan2
    adantr
    @107
    @121
    @122
    @111
    @130
    wceq
    @127
    @123
    @108
    @109
    omsuc
    syl2anc
    3eltr4d
    sseldd
    exp32
    a2d
    syl5
    expcom
    finds2
    syl3c
    eqeltrd
    sseldd
    rexlimdvaa
    wph
    cK
    com
    wcel
    #
    @0
    @7
    wo
    wph
    @34
    @33
    com
    wcel
    #
    @151
    cantnflt.k
    wph
    @142
    @152
    wph
    @141
    @142
    @143
    simprd
    @28
    peano2
    syl
    cK
    @33
    elnn
    syl2anc
    vx
    cK
    nn0suc
    syl
    mpjaod
end
