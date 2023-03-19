include "coe.mm"
include "co.mm"
include "cfv.mm"
include "comu.mm"
include "ccnf.mm"
include "wss.mm"
include "c0.mm"
include "wceq.mm"
include "oveq2.mm"
include "sseq1d.mm"
include "wne.mm"
include "wa.mm"
include "cdm.mm"
include "ccnv.mm"
include "wcel.mm"
include "csupp.mm"
include "wf1o.mm"
include "wf.mm"
include "cep.mm"
include "wiso.mm"
include "cvv.mm"
include "wwe.mm"
include "con0.mm"
include "suppssdm.mm"
include "cfsupp.mm"
include "wbr.mm"
include "cantnfs.mm"
include "mpbid.mm"
include "simpld.mm"
include "fdm.mm"
include "syl.mm"
include "syl5sseq.mm"
include "ssexd.mm"
include "com.mm"
include "cantnfcl.mm"
include "oiiso.mm"
include "syl2anc.mm"
include "isof1o.mm"
include "adantr.mm"
include "f1ocnv.mm"
include "f1of.mm"
include "3syl.mm"
include "anim1i.mm"
include "wfn.mm"
include "wb.mm"
include "ffn.mm"
include "0ex.mm"
include "a1i.mm"
include "elsuppfn.mm"
include "syl3anc.mm"
include "mpbird.mm"
include "ffvelrnd.mm"
include "wi.mm"
include "simprd.mm"
include "cv.mm"
include "eqimss.mm"
include "biantrurd.mm"
include "eleq2.mm"
include "bitr3d.mm"
include "fveq2.mm"
include "sseq2d.mm"
include "imbi12d.mm"
include "imbi2d.mm"
include "csuc.mm"
include "sseq1.mm"
include "anbi12d.mm"
include "noel.mm"
include "pm2.21i.mm"
include "adantl.mm"
include "wo.mm"
include "fvex.mm"
include "elsuc.mm"
include "sssucid.mm"
include "sstr.mm"
include "mpan.mm"
include "ad2antrl.mm"
include "simprr.mm"
include "pm2.27.mm"
include "coa.mm"
include "cantnfvalf.mm"
include "ffvelrni.mm"
include "ad2antlr.mm"
include "ad3antrrr.mm"
include "simpr.mm"
include "sucidg.mm"
include "sseldd.mm"
include "oif.mm"
include "onelon.mm"
include "oecl.mm"
include "omcl.mm"
include "oaword2.mm"
include "simplll.mm"
include "simplr.mm"
include "cantnfsuc.mm"
include "sseqtr4d.mm"
include "expcom.mm"
include "adantrr.mm"
include "syld.mm"
include "expr.mm"
include "fveq2d.mm"
include "f1ocnvfv2.mm"
include "ad2antrr.mm"
include "eqtr3d.mm"
include "oveq2d.mm"
include "oveq12d.mm"
include "oaword1.mm"
include "eqsstr3d.mm"
include "a1dd.mm"
include "jaod.mm"
include "syl5bi.mm"
include "expimpd.mm"
include "com23.mm"
include "finds2.mm"
include "vtoclga.mm"
include "mpcom.mm"
include "mpd.mm"
include "cantnfval.mm"
include "om0.mm"
include "0ss.mm"
include "syl6eqss.mm"
include "pm2.61ne.mm"

theorem cantnfle
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
  let cK: class K
  let cO: class O
  let cY: class Y
  let cX: class X
  assume cantnfs.s: |- S = dom ( A CNF B )
  assume cantnfs.a: |- ( ph -> A e. On )
  assume cantnfs.b: |- ( ph -> B e. On )
  assume cantnfcl.g: |- G = OrdIso ( _E , ( F supp (/) ) )
  assume cantnfcl.f: |- ( ph -> F e. S )
  assume cantnfval.h: |- H = seqom ( ( k e. _V , z e. _V |-> ( ( ( A ^o ( G ` k ) ) .o ( F ` ( G ` k ) ) ) +o z ) ) , (/) )
  assume cantnfle.c: |- ( ph -> C e. B )

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
  assert |- ( ph -> ( ( A ^o C ) .o ( F ` C ) ) C_ ( ( A CNF B ) ` F ) )

  proof
    wph
    cA
    cC
    coe
    co
    #
    cC
    cF
    cfv
    #
    comu
    co
    #
    cF
    cA
    cB
    ccnf
    co
    cfv
    #
    wss
    @0
    c0
    comu
    co
    #
    @3
    wss
    @1
    c0
    @1
    c0
    wceq
    @2
    @4
    @3
    @1
    c0
    @0
    comu
    oveq2
    sseq1d
    wph
    @1
    c0
    wne
    #
    wa
    #
    @2
    cG
    cdm
    #
    cH
    cfv
    #
    @3
    @6
    cC
    cG
    ccnv
    #
    cfv
    #
    @7
    wcel
    #
    @2
    @8
    wss
    #
    @6
    cF
    c0
    csupp
    co
    #
    @7
    cC
    @9
    @6
    @7
    @13
    cG
    wf1o
    #
    @13
    @7
    @9
    wf1o
    @13
    @7
    @9
    wf
    wph
    @14
    @5
    wph
    @7
    @13
    cep
    cep
    cG
    wiso
    #
    @14
    wph
    @13
    cvv
    wcel
    @13
    cep
    wwe
    #
    @15
    wph
    @13
    cB
    con0
    cantnfs.b
    wph
    cF
    cdm
    #
    @13
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
    @17
    cB
    wceq
    wph
    @18
    cF
    c0
    cfsupp
    wbr
    #
    wph
    cF
    cS
    wcel
    @18
    @19
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
    ssexd
    wph
    @16
    @7
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
    @13
    cep
    cG
    cvv
    cantnfcl.g
    oiiso
    syl2anc
    @7
    @13
    cep
    cep
    cG
    isof1o
    syl
    adantr
    #
    @7
    @13
    cG
    f1ocnv
    @13
    @7
    @9
    f1of
    3syl
    @6
    cC
    @13
    wcel
    #
    cC
    cB
    wcel
    #
    @5
    wa
    #
    wph
    @26
    @5
    cantnfle.c
    anim1i
    @6
    cF
    cB
    wfn
    #
    cB
    con0
    wcel
    #
    c0
    cvv
    wcel
    #
    @25
    @27
    wb
    @6
    @18
    @28
    wph
    @18
    @5
    @20
    adantr
    cB
    cA
    cF
    ffn
    syl
    wph
    @29
    @5
    cantnfs.b
    adantr
    @30
    @6
    0ex
    a1i
    cC
    cF
    con0
    cvv
    cB
    c0
    elsuppfn
    syl3anc
    mpbird
    #
    ffvelrnd
    @22
    @6
    @11
    @12
    wi
    #
    wph
    @22
    @5
    wph
    @16
    @22
    @23
    simprd
    adantr
    @6
    vx
    cv
    #
    @7
    wss
    #
    @10
    @33
    wcel
    #
    wa
    #
    @2
    @33
    cH
    cfv
    #
    wss
    #
    wi
    #
    wi
    @6
    @32
    wi
    vx
    @7
    com
    @33
    @7
    wceq
    #
    @39
    @32
    @6
    @40
    @36
    @11
    @38
    @12
    @40
    @35
    @36
    @11
    @40
    @34
    @35
    @33
    @7
    eqimss
    biantrurd
    @33
    @7
    @10
    eleq2
    bitr3d
    @40
    @37
    @8
    @2
    @33
    @7
    cH
    fveq2
    sseq2d
    imbi12d
    imbi2d
    @39
    c0
    @7
    wss
    #
    @10
    c0
    wcel
    #
    wa
    #
    @2
    c0
    cH
    cfv
    #
    wss
    #
    wi
    #
    vy
    cv
    #
    @7
    wss
    #
    @10
    @47
    wcel
    #
    wa
    #
    @2
    @47
    cH
    cfv
    #
    wss
    #
    wi
    #
    @47
    csuc
    #
    @7
    wss
    #
    @10
    @54
    wcel
    #
    wa
    #
    @2
    @54
    cH
    cfv
    #
    wss
    #
    wi
    #
    @6
    vx
    vy
    @33
    c0
    wceq
    #
    @36
    @43
    @38
    @45
    @61
    @34
    @41
    @35
    @42
    @33
    c0
    @7
    sseq1
    @33
    c0
    @10
    eleq2
    anbi12d
    @61
    @37
    @44
    @2
    @33
    c0
    cH
    fveq2
    sseq2d
    imbi12d
    @33
    @47
    wceq
    #
    @36
    @50
    @38
    @52
    @62
    @34
    @48
    @35
    @49
    @33
    @47
    @7
    sseq1
    @33
    @47
    @10
    eleq2
    anbi12d
    @62
    @37
    @51
    @2
    @33
    @47
    cH
    fveq2
    sseq2d
    imbi12d
    @33
    @54
    wceq
    #
    @36
    @57
    @38
    @59
    @63
    @34
    @55
    @35
    @56
    @33
    @54
    @7
    sseq1
    @33
    @54
    @10
    eleq2
    anbi12d
    @63
    @37
    @58
    @2
    @33
    @54
    cH
    fveq2
    sseq2d
    imbi12d
    @46
    @6
    @42
    @45
    @41
    @42
    @45
    @10
    noel
    pm2.21i
    adantl
    a1i
    @6
    @47
    com
    wcel
    #
    @53
    @60
    wi
    @6
    @64
    wa
    #
    @57
    @53
    @59
    @65
    @55
    @56
    @53
    @59
    wi
    #
    @56
    @49
    @10
    @47
    wceq
    #
    wo
    @65
    @55
    wa
    #
    @66
    @10
    @47
    cC
    @9
    fvex
    elsuc
    @68
    @49
    @66
    @67
    @65
    @55
    @49
    @66
    @65
    @55
    @49
    wa
    wa
    #
    @53
    @52
    @59
    @69
    @48
    @49
    @53
    @52
    wi
    @55
    @48
    @65
    @49
    @47
    @54
    wss
    @55
    @48
    @47
    sssucid
    @47
    @54
    @7
    sstr
    mpan
    ad2antrl
    @65
    @55
    @49
    simprr
    @50
    @52
    pm2.27
    syl2anc
    @65
    @55
    @52
    @59
    wi
    #
    @49
    @68
    @51
    @58
    wss
    #
    @70
    @68
    @51
    cA
    @47
    cG
    cfv
    #
    coe
    co
    #
    @72
    cF
    cfv
    #
    comu
    co
    #
    @51
    coa
    co
    #
    @58
    @68
    @51
    con0
    wcel
    #
    @75
    con0
    wcel
    #
    @51
    @76
    wss
    @64
    @77
    @6
    @55
    com
    con0
    @47
    cH
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
    @79
    cF
    cfv
    comu
    co
    vz
    cv
    vk
    cH
    cantnfval.h
    cantnfvalf
    ffvelrni
    ad2antlr
    #
    @68
    @73
    con0
    wcel
    #
    @74
    con0
    wcel
    #
    @78
    @68
    cA
    con0
    wcel
    #
    @72
    con0
    wcel
    #
    @81
    wph
    @83
    @5
    @64
    @55
    cantnfs.a
    ad3antrrr
    #
    @68
    @29
    @72
    cB
    wcel
    @84
    wph
    @29
    @5
    @64
    @55
    cantnfs.b
    ad3antrrr
    @68
    @13
    cB
    @72
    wph
    @13
    cB
    wss
    @5
    @64
    @55
    @21
    ad3antrrr
    @68
    @47
    @7
    wcel
    @72
    @13
    wcel
    @68
    @54
    @7
    @47
    @65
    @55
    simpr
    @64
    @47
    @54
    wcel
    @6
    @55
    @47
    com
    sucidg
    ad2antlr
    sseldd
    @7
    @13
    @47
    cG
    @13
    cep
    cG
    cantnfcl.g
    oif
    ffvelrni
    syl
    sseldd
    #
    cB
    @72
    onelon
    syl2anc
    cA
    @72
    oecl
    syl2anc
    @68
    @83
    @74
    cA
    wcel
    @82
    @85
    @68
    cB
    cA
    @72
    cF
    wph
    @18
    @5
    @64
    @55
    @20
    ad3antrrr
    @86
    ffvelrnd
    cA
    @74
    onelon
    syl2anc
    @73
    @74
    omcl
    syl2anc
    #
    @51
    @75
    oaword2
    syl2anc
    @68
    wph
    @64
    @58
    @76
    wceq
    #
    wph
    @5
    @64
    @55
    simplll
    @6
    @64
    @55
    simplr
    wph
    vz
    cA
    cB
    cS
    vk
    cF
    cG
    cH
    @47
    cantnfs.s
    cantnfs.a
    cantnfs.b
    cantnfcl.g
    cantnfcl.f
    cantnfval.h
    cantnfsuc
    syl2anc
    #
    sseqtr4d
    @52
    @71
    @59
    @2
    @51
    @58
    sstr
    expcom
    syl
    adantrr
    syld
    expr
    @68
    @67
    @59
    @53
    @65
    @55
    @67
    @59
    @65
    @55
    @67
    wa
    #
    wa
    #
    @2
    @76
    @58
    @91
    @2
    @75
    @76
    @91
    @73
    @0
    @74
    @1
    comu
    @91
    @72
    cC
    cA
    coe
    @91
    @10
    cG
    cfv
    #
    @72
    cC
    @91
    @10
    @47
    cG
    @65
    @55
    @67
    simprr
    fveq2d
    @6
    @92
    cC
    wceq
    #
    @64
    @90
    @6
    @14
    @25
    @93
    @24
    @31
    @7
    @13
    cC
    cG
    f1ocnvfv2
    syl2anc
    ad2antrr
    eqtr3d
    #
    oveq2d
    @91
    @72
    cC
    cF
    @94
    fveq2d
    oveq12d
    @65
    @55
    @75
    @76
    wss
    #
    @67
    @68
    @78
    @77
    @95
    @87
    @80
    @75
    @51
    oaword1
    syl2anc
    adantrr
    eqsstr3d
    @65
    @55
    @88
    @67
    @89
    adantrr
    sseqtr4d
    expr
    a1dd
    jaod
    syl5bi
    expimpd
    com23
    expcom
    finds2
    vtoclga
    mpcom
    mpd
    wph
    @3
    @8
    wceq
    @5
    wph
    vz
    cA
    cB
    cS
    vk
    cF
    cG
    cH
    cantnfs.s
    cantnfs.a
    cantnfs.b
    cantnfcl.g
    cantnfcl.f
    cantnfval.h
    cantnfval
    adantr
    sseqtr4d
    wph
    @4
    c0
    @3
    wph
    @0
    con0
    wcel
    #
    @4
    c0
    wceq
    wph
    @83
    cC
    con0
    wcel
    #
    @96
    cantnfs.a
    wph
    @29
    @26
    @97
    cantnfs.b
    cantnfle.c
    cB
    cC
    onelon
    syl2anc
    cA
    cC
    oecl
    syl2anc
    @0
    om0
    syl
    @3
    0ss
    syl6eqss
    pm2.61ne
end
