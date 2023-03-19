include "coe.mm"
include "co.mm"
include "cfv.mm"
include "comu.mm"
include "ccnv.mm"
include "csuc.mm"
include "cv.mm"
include "wss.mm"
include "c0.mm"
include "cif.mm"
include "cmpt.mm"
include "ccnf.mm"
include "coa.mm"
include "con0.mm"
include "wcel.mm"
include "wceq.mm"
include "wi.mm"
include "wral.mm"
include "oemapvali.mm"
include "simp1d.mm"
include "onelon.mm"
include "syl2anc.mm"
include "oecl.mm"
include "wf.mm"
include "cfsupp.mm"
include "wbr.mm"
include "wa.mm"
include "cantnfs.mm"
include "mpbid.mm"
include "simpld.mm"
include "ffvelrnd.mm"
include "omcl.mm"
include "com.mm"
include "cdm.mm"
include "csupp.mm"
include "wf1o.mm"
include "cep.mm"
include "wiso.mm"
include "cvv.mm"
include "wwe.mm"
include "suppssdm.mm"
include "fdm.mm"
include "syl.mm"
include "syl5sseq.mm"
include "ssexd.mm"
include "cantnfcl.mm"
include "oiiso.mm"
include "isof1o.mm"
include "f1ocnv.mm"
include "f1of.mm"
include "3syl.mm"
include "cantnflem1a.mm"
include "simprd.mm"
include "elnn.mm"
include "cantnfvalf.mm"
include "ffvelrni.mm"
include "oaword1.mm"
include "cantnfsuc.mm"
include "mpdan.mm"
include "f1ocnvfv2.mm"
include "oveq2d.mm"
include "fveq2d.mm"
include "oveq12d.mm"
include "oveq1d.mm"
include "eqtrd.mm"
include "sseqtr4d.mm"
include "wo.mm"
include "wb.mm"
include "onss.mm"
include "sselda.mm"
include "adantr.mm"
include "onsseleq.mm"
include "orcom.mm"
include "syl6bb.mm"
include "ifbid.mm"
include "mpteq2dva.mm"
include "ffvelrnda.mm"
include "wne.mm"
include "ne0i.mm"
include "on0eln0.mm"
include "mpbird.mm"
include "ifcld.mm"
include "eqid.mm"
include "fmptd.mm"
include "0ex.mm"
include "a1i.mm"
include "fsuppmptif.mm"
include "mpbir2and.mm"
include "cdif.mm"
include "wn.mm"
include "eldifn.mm"
include "adantl.mm"
include "iffalsed.mm"
include "suppss2.mm"
include "fveq2.mm"
include "ifeq1da.mm"
include "eleq1.mm"
include "ifbieq1d.mm"
include "fvex.mm"
include "ifex.mm"
include "fvmpt.mm"
include "ifeq2d.mm"
include "eqtr3d.mm"
include "ifor.mm"
include "syl6reqr.mm"
include "mpteq2ia.mm"
include "cantnfp1.mm"
include "omsuc.mm"
include "word.mm"
include "eloni.mm"
include "simp2d.mm"
include "ordsucss.mm"
include "sylc.mm"
include "suceloni.mm"
include "omwordi.mm"
include "syl3anc.mm"
include "mpd.mm"
include "eqsstr3d.mm"
include "cantnflt2.mm"
include "oaord.mm"
include "sseldd.mm"
include "eqeltrd.mm"

theorem cantnflem1d
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vw: setvar w
  let cA: class A
  let cB: class B
  let cS: class S
  let cT: class T
  let vk: setvar k
  let cF: class F
  let cG: class G
  let cH: class H
  let cO: class O
  let cX: class X
  let vc: setvar c
  let vf: setvar f
  let vg: setvar g
  let vh: setvar h
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
  let cZ: class Z
  let cK: class K
  let cY: class Y
  assume cantnfs.s: |- S = dom ( A CNF B )
  assume cantnfs.a: |- ( ph -> A e. On )
  assume cantnfs.b: |- ( ph -> B e. On )
  assume oemapval.t: |- T = { <. x , y >. | E. z e. B ( ( x ` z ) e. ( y ` z ) /\ A. w e. B ( z e. w -> ( x ` w ) = ( y ` w ) ) ) }
  assume oemapval.f: |- ( ph -> F e. S )
  assume oemapval.g: |- ( ph -> G e. S )
  assume oemapvali.r: |- ( ph -> F T G )
  assume oemapvali.x: |- X = U. { c e. B | ( F ` c ) e. ( G ` c ) }
  assume cantnflem1.o: |- O = OrdIso ( _E , ( G supp (/) ) )
  assume cantnflem1.h: |- H = seqom ( ( k e. _V , z e. _V |-> ( ( ( A ^o ( O ` k ) ) .o ( G ` ( O ` k ) ) ) +o z ) ) , (/) )

  disjoint F c
  disjoint c ph
  disjoint c k
  disjoint c w
  disjoint c x
  disjoint c y
  disjoint c z
  disjoint B c
  disjoint k w
  disjoint k x
  disjoint k y
  disjoint k z
  disjoint B k
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
  disjoint A c
  disjoint A k
  disjoint A w
  disjoint A x
  disjoint A y
  disjoint A z
  disjoint T c
  disjoint T k
  disjoint F k
  disjoint F w
  disjoint F x
  disjoint F y
  disjoint F z
  disjoint S c
  disjoint S k
  disjoint S x
  disjoint S y
  disjoint S z
  disjoint G c
  disjoint G k
  disjoint G w
  disjoint G x
  disjoint G y
  disjoint G z
  disjoint H x
  disjoint H y
  disjoint O k
  disjoint O w
  disjoint O x
  disjoint O y
  disjoint O z
  disjoint k ph
  disjoint ph x
  disjoint ph y
  disjoint ph z
  disjoint X k
  disjoint X w
  disjoint X x
  disjoint X y
  disjoint X z
  disjoint c f
  disjoint c g
  disjoint c h
  disjoint c n
  disjoint c t
  disjoint c u
  disjoint c v
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
  disjoint M x
  disjoint M y
  disjoint T f
  disjoint T g
  disjoint T t
  disjoint T u
  disjoint T v
  disjoint F f
  disjoint F g
  disjoint F h
  disjoint F u
  disjoint F v
  disjoint S f
  disjoint S g
  disjoint S t
  disjoint S u
  disjoint S v
  disjoint Z g
  disjoint Z t
  disjoint Z x
  disjoint Z y
  disjoint Z z
  disjoint G f
  disjoint G h
  disjoint G t
  disjoint G u
  disjoint G v
  disjoint H f
  disjoint H h
  disjoint H u
  disjoint H v
  disjoint K k
  disjoint K t
  disjoint K u
  disjoint K v
  disjoint K x
  disjoint K z
  disjoint O u
  disjoint f ph
  disjoint g ph
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
  disjoint X t
  disjoint X u
  assert |- ( ph -> ( ( A CNF B ) ` ( x e. B |-> if ( x C_ X , ( F ` x ) , (/) ) ) ) e. ( H ` suc ( `' O ` X ) ) )

  proof
    wph
    cA
    cX
    coe
    co
    #
    cX
    cG
    cfv
    #
    comu
    co
    #
    cX
    cO
    ccnv
    #
    cfv
    #
    csuc
    cH
    cfv
    #
    vx
    cB
    vx
    cv
    #
    cX
    wss
    #
    @6
    cF
    cfv
    #
    c0
    cif
    #
    cmpt
    #
    cA
    cB
    ccnf
    co
    #
    cfv
    #
    wph
    @2
    @2
    @4
    cH
    cfv
    #
    coa
    co
    #
    @5
    wph
    @2
    con0
    wcel
    #
    @13
    con0
    wcel
    #
    @2
    @14
    wss
    wph
    @0
    con0
    wcel
    #
    @1
    con0
    wcel
    #
    @15
    wph
    cA
    con0
    wcel
    #
    cX
    con0
    wcel
    #
    @17
    cantnfs.a
    wph
    cB
    con0
    wcel
    #
    cX
    cB
    wcel
    #
    @20
    cantnfs.b
    wph
    @22
    cX
    cF
    cfv
    #
    @1
    wcel
    #
    cX
    vw
    cv
    #
    wcel
    @25
    cF
    cfv
    @25
    cG
    cfv
    wceq
    wi
    vw
    cB
    wral
    #
    wph
    vx
    vy
    vz
    vw
    cA
    cB
    cS
    cT
    cF
    cG
    cX
    vc
    cantnfs.s
    cantnfs.a
    cantnfs.b
    oemapval.t
    oemapval.f
    oemapval.g
    oemapvali.r
    oemapvali.x
    oemapvali
    #
    simp1d
    #
    cB
    cX
    onelon
    syl2anc
    #
    cA
    cX
    oecl
    syl2anc
    #
    wph
    @19
    @1
    cA
    wcel
    #
    @18
    cantnfs.a
    wph
    cB
    cA
    cX
    cG
    wph
    cB
    cA
    cG
    wf
    #
    cG
    c0
    cfsupp
    wbr
    #
    wph
    cG
    cS
    wcel
    @32
    @33
    wa
    oemapval.g
    wph
    cA
    cB
    cS
    cG
    cantnfs.s
    cantnfs.a
    cantnfs.b
    cantnfs
    mpbid
    simpld
    #
    @28
    ffvelrnd
    #
    cA
    @1
    onelon
    syl2anc
    #
    @0
    @1
    omcl
    syl2anc
    wph
    @4
    com
    wcel
    #
    @16
    wph
    @4
    cO
    cdm
    #
    wcel
    @38
    com
    wcel
    #
    @37
    wph
    cG
    c0
    csupp
    co
    #
    @38
    cX
    @3
    wph
    @38
    @40
    cO
    wf1o
    #
    @40
    @38
    @3
    wf1o
    @40
    @38
    @3
    wf
    wph
    @38
    @40
    cep
    cep
    cO
    wiso
    #
    @41
    wph
    @40
    cvv
    wcel
    @40
    cep
    wwe
    #
    @42
    wph
    @40
    cB
    con0
    cantnfs.b
    wph
    cG
    cdm
    #
    @40
    cB
    cG
    c0
    suppssdm
    wph
    @32
    @44
    cB
    wceq
    @34
    cB
    cA
    cG
    fdm
    syl
    syl5sseq
    ssexd
    wph
    @43
    @39
    wph
    cA
    cB
    cS
    cG
    cO
    cantnfs.s
    cantnfs.a
    cantnfs.b
    cantnflem1.o
    oemapval.g
    cantnfcl
    #
    simpld
    @40
    cep
    cO
    cvv
    cantnflem1.o
    oiiso
    syl2anc
    @38
    @40
    cep
    cep
    cO
    isof1o
    syl
    #
    @38
    @40
    cO
    f1ocnv
    @40
    @38
    @3
    f1of
    3syl
    wph
    vx
    vy
    vz
    vw
    cA
    cB
    cS
    cT
    cF
    cG
    cX
    vc
    cantnfs.s
    cantnfs.a
    cantnfs.b
    oemapval.t
    oemapval.f
    oemapval.g
    oemapvali.r
    oemapvali.x
    cantnflem1a
    #
    ffvelrnd
    wph
    @43
    @39
    @45
    simprd
    @4
    @38
    elnn
    syl2anc
    #
    com
    con0
    @4
    cH
    vz
    cvv
    cvv
    cA
    vk
    cv
    cO
    cfv
    #
    coe
    co
    @49
    cG
    cfv
    comu
    co
    vz
    cv
    vk
    cH
    cantnflem1.h
    cantnfvalf
    ffvelrni
    syl
    @2
    @13
    oaword1
    syl2anc
    wph
    @5
    cA
    @4
    cO
    cfv
    #
    coe
    co
    #
    @50
    cG
    cfv
    #
    comu
    co
    #
    @13
    coa
    co
    #
    @14
    wph
    @37
    @5
    @54
    wceq
    @48
    wph
    vz
    cA
    cB
    cS
    vk
    cG
    cO
    cH
    @4
    cantnfs.s
    cantnfs.a
    cantnfs.b
    cantnflem1.o
    oemapval.g
    cantnflem1.h
    cantnfsuc
    mpdan
    wph
    @53
    @2
    @13
    coa
    wph
    @51
    @0
    @52
    @1
    comu
    wph
    @50
    cX
    cA
    coe
    wph
    @41
    cX
    @40
    wcel
    @50
    cX
    wceq
    @46
    @47
    @38
    @40
    cX
    cO
    f1ocnvfv2
    syl2anc
    #
    oveq2d
    wph
    @50
    cX
    cG
    @55
    fveq2d
    oveq12d
    oveq1d
    eqtrd
    sseqtr4d
    wph
    @12
    @0
    @23
    comu
    co
    #
    vy
    cB
    vy
    cv
    #
    cX
    wcel
    #
    @57
    cF
    cfv
    #
    c0
    cif
    #
    cmpt
    #
    @11
    cfv
    #
    coa
    co
    #
    @2
    wph
    @12
    vx
    cB
    @6
    cX
    wceq
    #
    @6
    cX
    wcel
    #
    wo
    #
    @8
    c0
    cif
    #
    cmpt
    #
    @11
    cfv
    #
    @63
    wph
    @10
    @68
    @11
    wph
    vx
    cB
    @9
    @67
    wph
    @6
    cB
    wcel
    #
    wa
    #
    @7
    @66
    @8
    c0
    @71
    @7
    @65
    @64
    wo
    #
    @66
    @71
    @6
    con0
    wcel
    @20
    @7
    @72
    wb
    wph
    cB
    con0
    @6
    wph
    @21
    cB
    con0
    wss
    cantnfs.b
    cB
    onss
    syl
    sselda
    wph
    @20
    @70
    @29
    adantr
    @6
    cX
    onsseleq
    syl2anc
    @65
    @64
    orcom
    syl6bb
    ifbid
    mpteq2dva
    fveq2d
    wph
    @68
    cS
    wcel
    @69
    @63
    wceq
    wph
    vx
    cA
    cB
    cS
    @68
    @61
    cX
    @23
    cantnfs.s
    cantnfs.a
    cantnfs.b
    wph
    @61
    cS
    wcel
    cB
    cA
    @61
    wf
    @61
    c0
    cfsupp
    wbr
    wph
    vy
    cB
    @60
    cA
    @61
    wph
    @57
    cB
    wcel
    #
    wa
    @58
    @59
    c0
    cA
    wph
    cB
    cA
    @57
    cF
    wph
    cB
    cA
    cF
    wf
    #
    cF
    c0
    cfsupp
    wbr
    #
    wph
    cF
    cS
    wcel
    @74
    @75
    wa
    oemapval.f
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
    #
    simpld
    #
    ffvelrnda
    wph
    c0
    cA
    wcel
    #
    @73
    wph
    @78
    cA
    c0
    wne
    #
    wph
    @31
    @79
    @35
    cA
    @1
    ne0i
    syl
    wph
    @19
    @78
    @79
    wb
    cantnfs.a
    cA
    on0eln0
    syl
    mpbird
    #
    adantr
    ifcld
    @61
    eqid
    #
    fmptd
    wph
    cB
    cA
    cX
    vy
    cF
    con0
    cvv
    c0
    @77
    cantnfs.b
    c0
    cvv
    wcel
    wph
    0ex
    a1i
    wph
    @74
    @75
    @76
    simprd
    fsuppmptif
    wph
    cA
    cB
    cS
    @61
    cantnfs.s
    cantnfs.a
    cantnfs.b
    cantnfs
    mpbir2and
    #
    @28
    wph
    cB
    cA
    cX
    cF
    @77
    @28
    ffvelrnd
    #
    wph
    cB
    @60
    vy
    con0
    cX
    c0
    wph
    @57
    cB
    cX
    cdif
    wcel
    #
    wa
    @58
    @59
    c0
    @84
    @58
    wn
    wph
    @57
    cB
    cX
    eldifn
    adantl
    iffalsed
    cantnfs.b
    suppss2
    #
    vx
    cB
    @67
    @64
    @23
    @6
    @61
    cfv
    #
    cif
    #
    @70
    @87
    @64
    @8
    @65
    @8
    c0
    cif
    #
    cif
    #
    @67
    @70
    @64
    @8
    @86
    cif
    @87
    @89
    @70
    @64
    @8
    @23
    @86
    @64
    @8
    @23
    wceq
    @70
    @6
    cX
    cF
    fveq2
    adantl
    ifeq1da
    @70
    @64
    @86
    @88
    @8
    vy
    @6
    @60
    @88
    cB
    @61
    @57
    @6
    wceq
    @58
    @65
    @59
    @8
    c0
    @57
    @6
    cX
    eleq1
    @57
    @6
    cF
    fveq2
    ifbieq1d
    @81
    @65
    @8
    c0
    @6
    cF
    fvex
    0ex
    ifex
    fvmpt
    ifeq2d
    eqtr3d
    @64
    @65
    @8
    c0
    ifor
    syl6reqr
    mpteq2ia
    cantnfp1
    simprd
    eqtrd
    wph
    @56
    @0
    coa
    co
    #
    @2
    @63
    wph
    @90
    @0
    @23
    csuc
    #
    comu
    co
    #
    @2
    wph
    @17
    @23
    con0
    wcel
    #
    @92
    @90
    wceq
    @30
    wph
    @19
    @23
    cA
    wcel
    @93
    cantnfs.a
    @83
    cA
    @23
    onelon
    syl2anc
    #
    @0
    @23
    omsuc
    syl2anc
    wph
    @91
    @1
    wss
    #
    @92
    @2
    wss
    #
    wph
    @1
    word
    #
    @24
    @95
    wph
    @18
    @97
    @36
    @1
    eloni
    syl
    wph
    @22
    @24
    @26
    @27
    simp2d
    @23
    @1
    ordsucss
    sylc
    wph
    @91
    con0
    wcel
    #
    @18
    @17
    @95
    @96
    wi
    wph
    @93
    @98
    @94
    @23
    suceloni
    syl
    @36
    @30
    @91
    @1
    @0
    omwordi
    syl3anc
    mpd
    eqsstr3d
    wph
    @62
    @0
    wcel
    #
    @63
    @90
    wcel
    #
    wph
    cA
    cB
    cX
    cS
    @61
    cantnfs.s
    cantnfs.a
    cantnfs.b
    @82
    @80
    @29
    @85
    cantnflt2
    #
    wph
    @62
    con0
    wcel
    #
    @17
    @56
    con0
    wcel
    #
    @99
    @100
    wb
    wph
    @17
    @99
    @102
    @30
    @101
    @0
    @62
    onelon
    syl2anc
    @30
    wph
    @17
    @93
    @103
    @30
    @94
    @0
    @23
    omcl
    syl2anc
    @62
    @0
    @56
    oaord
    syl3anc
    mpbid
    sseldd
    eqeltrd
    sseldd
end
