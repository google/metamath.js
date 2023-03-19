include "cv.mm"
include "csuc.mm"
include "cdm.mm"
include "wcel.mm"
include "ccnv.mm"
include "cfv.mm"
include "wss.mm"
include "wa.mm"
include "wn.mm"
include "simprr.mm"
include "con0.mm"
include "wb.mm"
include "word.mm"
include "c0.mm"
include "csupp.mm"
include "co.mm"
include "cep.mm"
include "oicl.mm"
include "wf1o.mm"
include "wf.mm"
include "wiso.mm"
include "cvv.mm"
include "wwe.mm"
include "suppssdm.mm"
include "wceq.mm"
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
include "f1ocnv.mm"
include "f1of.mm"
include "3syl.mm"
include "cantnflem1a.mm"
include "ffvelrnd.mm"
include "ordelon.mm"
include "sylancr.mm"
include "adantr.mm"
include "a1i.mm"
include "sylan.mm"
include "sucelon.mm"
include "sylibr.mm"
include "adantrr.mm"
include "ontri1.mm"
include "wtr.mm"
include "ordtr.mm"
include "mp1i.mm"
include "simprl.mm"
include "trsuc.mm"
include "isorel.mm"
include "syl12anc.mm"
include "fvex.mm"
include "epelc.mm"
include "3bitr3g.mm"
include "f1ocnvfv2.mm"
include "eleq2d.mm"
include "bitrd.mm"
include "mtbid.mm"
include "wi.mm"
include "wral.mm"
include "oemapvali.mm"
include "simp1d.mm"
include "onelon.mm"
include "oif.mm"
include "ffvelrni.mm"
include "sseldd.mm"
include "mpbird.mm"

theorem cantnflem1b
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vw: setvar w
  let vu: setvar u
  let cA: class A
  let cB: class B
  let cS: class S
  let cT: class T
  let cF: class F
  let cG: class G
  let cO: class O
  let cX: class X
  let vc: setvar c
  let vf: setvar f
  let vg: setvar g
  let vh: setvar h
  let vk: setvar k
  let vn: setvar n
  let vt: setvar t
  let vv: setvar v
  let va: setvar a
  let vb: setvar b
  let vd: setvar d
  let cC: class C
  let cD: class D
  let cM: class M
  let cZ: class Z
  let cH: class H
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

  disjoint F c
  disjoint c ph
  disjoint c u
  disjoint c w
  disjoint c x
  disjoint c y
  disjoint c z
  disjoint B c
  disjoint u w
  disjoint u x
  disjoint u y
  disjoint u z
  disjoint B u
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
  disjoint A u
  disjoint A w
  disjoint A x
  disjoint A y
  disjoint A z
  disjoint T c
  disjoint T u
  disjoint F u
  disjoint F w
  disjoint F x
  disjoint F y
  disjoint F z
  disjoint S c
  disjoint S u
  disjoint S x
  disjoint S y
  disjoint S z
  disjoint G c
  disjoint G u
  disjoint G w
  disjoint G x
  disjoint G y
  disjoint G z
  disjoint O u
  disjoint O w
  disjoint O x
  disjoint O y
  disjoint O z
  disjoint ph u
  disjoint ph x
  disjoint ph y
  disjoint ph z
  disjoint X u
  disjoint X w
  disjoint X x
  disjoint X y
  disjoint X z
  disjoint c f
  disjoint c g
  disjoint c h
  disjoint c k
  disjoint c n
  disjoint c t
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
  disjoint A k
  disjoint A n
  disjoint A t
  disjoint A v
  disjoint M x
  disjoint M y
  disjoint T f
  disjoint T g
  disjoint T k
  disjoint T t
  disjoint T v
  disjoint F f
  disjoint F g
  disjoint F h
  disjoint F k
  disjoint F v
  disjoint S f
  disjoint S g
  disjoint S k
  disjoint S t
  disjoint S v
  disjoint Z g
  disjoint Z t
  disjoint Z x
  disjoint Z y
  disjoint Z z
  disjoint G f
  disjoint G h
  disjoint G k
  disjoint G t
  disjoint G v
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
  disjoint f ph
  disjoint g ph
  disjoint k ph
  disjoint n ph
  disjoint ph t
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
  assert |- ( ( ph /\ ( suc u e. dom O /\ ( `' O ` X ) C_ u ) ) -> X C_ ( O ` u ) )

  proof
    wph
    vu
    cv
    #
    csuc
    #
    cO
    cdm
    #
    wcel
    #
    cX
    cO
    ccnv
    #
    cfv
    #
    @0
    wss
    #
    wa
    #
    wa
    #
    cX
    @0
    cO
    cfv
    #
    wss
    #
    @9
    cX
    wcel
    #
    wn
    #
    @8
    @0
    @5
    wcel
    #
    @11
    @8
    @6
    @13
    wn
    #
    wph
    @3
    @6
    simprr
    @8
    @5
    con0
    wcel
    #
    @0
    con0
    wcel
    #
    @6
    @14
    wb
    wph
    @15
    @7
    wph
    @2
    word
    #
    @5
    @2
    wcel
    #
    @15
    cG
    c0
    csupp
    co
    #
    cep
    cO
    cantnflem1.o
    oicl
    #
    wph
    @19
    @2
    cX
    @4
    wph
    @2
    @19
    cO
    wf1o
    #
    @19
    @2
    @4
    wf1o
    @19
    @2
    @4
    wf
    wph
    @2
    @19
    cep
    cep
    cO
    wiso
    #
    @21
    wph
    @19
    cvv
    wcel
    @19
    cep
    wwe
    #
    @22
    wph
    @19
    cB
    con0
    cantnfs.b
    wph
    cG
    cdm
    #
    @19
    cB
    cG
    c0
    suppssdm
    wph
    cB
    cA
    cG
    wf
    #
    @24
    cB
    wceq
    wph
    @25
    cG
    c0
    cfsupp
    wbr
    #
    wph
    cG
    cS
    wcel
    @25
    @26
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
    cB
    cA
    cG
    fdm
    syl
    syl5sseq
    #
    ssexd
    wph
    @23
    @2
    com
    wcel
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
    simpld
    @19
    cep
    cO
    cvv
    cantnflem1.o
    oiiso
    syl2anc
    #
    @2
    @19
    cep
    cep
    cO
    isof1o
    syl
    #
    @2
    @19
    cO
    f1ocnv
    @19
    @2
    @4
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
    #
    @2
    @5
    ordelon
    sylancr
    adantr
    wph
    @3
    @16
    @6
    wph
    @3
    wa
    @1
    con0
    wcel
    #
    @16
    wph
    @17
    @3
    @32
    @17
    wph
    @20
    a1i
    @2
    @1
    ordelon
    sylan
    @0
    sucelon
    sylibr
    adantrr
    @5
    @0
    ontri1
    syl2anc
    mpbid
    @8
    @13
    @9
    @5
    cO
    cfv
    #
    wcel
    #
    @11
    @8
    @0
    @5
    cep
    wbr
    #
    @9
    @33
    cep
    wbr
    #
    @13
    @34
    @8
    @22
    @0
    @2
    wcel
    #
    @18
    @35
    @36
    wb
    wph
    @22
    @7
    @28
    adantr
    @8
    @2
    wtr
    #
    @3
    @37
    @17
    @38
    @8
    @20
    @2
    ordtr
    mp1i
    wph
    @3
    @6
    simprl
    @2
    @0
    trsuc
    syl2anc
    #
    wph
    @18
    @7
    @31
    adantr
    @2
    @19
    @0
    @5
    cep
    cep
    cO
    isorel
    syl12anc
    @0
    @5
    cX
    @4
    fvex
    epelc
    @9
    @33
    @5
    cO
    fvex
    epelc
    3bitr3g
    @8
    @33
    cX
    @9
    wph
    @33
    cX
    wceq
    #
    @7
    wph
    @21
    cX
    @19
    wcel
    @40
    @29
    @30
    @2
    @19
    cX
    cO
    f1ocnvfv2
    syl2anc
    adantr
    eleq2d
    bitrd
    mtbid
    @8
    cX
    con0
    wcel
    #
    @9
    con0
    wcel
    #
    @10
    @12
    wb
    wph
    @41
    @7
    wph
    cB
    con0
    wcel
    #
    cX
    cB
    wcel
    #
    @41
    cantnfs.b
    wph
    @44
    cX
    cF
    cfv
    cX
    cG
    cfv
    wcel
    cX
    vw
    cv
    #
    wcel
    @45
    cF
    cfv
    @45
    cG
    cfv
    wceq
    wi
    vw
    cB
    wral
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
    simp1d
    cB
    cX
    onelon
    syl2anc
    adantr
    @8
    @43
    @9
    cB
    wcel
    @42
    wph
    @43
    @7
    cantnfs.b
    adantr
    @8
    @19
    cB
    @9
    wph
    @19
    cB
    wss
    @7
    @27
    adantr
    @8
    @37
    @9
    @19
    wcel
    @39
    @2
    @19
    @0
    cO
    @19
    cep
    cO
    cantnflem1.o
    oif
    ffvelrni
    syl
    sseldd
    cB
    @9
    onelon
    syl2anc
    cX
    @9
    ontri1
    syl2anc
    mpbird
end
