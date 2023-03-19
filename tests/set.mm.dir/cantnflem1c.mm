include "cv.mm"
include "csuc.mm"
include "cdm.mm"
include "wcel.mm"
include "ccnv.mm"
include "cfv.mm"
include "wss.mm"
include "wa.mm"
include "c0.mm"
include "wne.mm"
include "con0.mm"
include "wfn.mm"
include "csupp.mm"
include "co.mm"
include "ad3antrrr.mm"
include "simplr.mm"
include "wf.mm"
include "cfsupp.mm"
include "wbr.mm"
include "cantnfs.mm"
include "mpbid.mm"
include "simpld.mm"
include "ffn.mm"
include "syl.mm"
include "wceq.mm"
include "wi.mm"
include "wral.mm"
include "oemapvali.mm"
include "simp3d.mm"
include "cantnflem1b.mm"
include "ad2antrr.mm"
include "simprr.mm"
include "simp1d.mm"
include "onelon.mm"
include "syl2anc.mm"
include "onss.mm"
include "sselda.mm"
include "adantlr.mm"
include "adantr.mm"
include "ontr2.mm"
include "mp2and.mm"
include "eleq2.mm"
include "fveq2.mm"
include "eqeq12d.mm"
include "imbi12d.mm"
include "rspcv.mm"
include "syl3c.mm"
include "simprl.mm"
include "eqnetrrd.mm"
include "fvn0elsupp.mm"
include "syl22anc.mm"

theorem cantnflem1c
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
  assert |- ( ( ( ( ph /\ ( suc u e. dom O /\ ( `' O ` X ) C_ u ) ) /\ x e. B ) /\ ( ( F ` x ) =/= (/) /\ ( O ` u ) e. x ) ) -> x e. ( G supp (/) ) )

  proof
    wph
    vu
    cv
    #
    csuc
    cO
    cdm
    wcel
    cX
    cO
    ccnv
    cfv
    @0
    wss
    wa
    #
    wa
    #
    vx
    cv
    #
    cB
    wcel
    #
    wa
    #
    @3
    cF
    cfv
    #
    c0
    wne
    #
    @0
    cO
    cfv
    #
    @3
    wcel
    #
    wa
    #
    wa
    #
    cB
    con0
    wcel
    #
    @4
    cG
    cB
    wfn
    #
    @3
    cG
    cfv
    #
    c0
    wne
    @3
    cG
    c0
    csupp
    co
    wcel
    wph
    @12
    @1
    @4
    @10
    cantnfs.b
    ad3antrrr
    @2
    @4
    @10
    simplr
    #
    wph
    @13
    @1
    @4
    @10
    wph
    cB
    cA
    cG
    wf
    #
    @13
    wph
    @16
    cG
    c0
    cfsupp
    wbr
    #
    wph
    cG
    cS
    wcel
    @16
    @17
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
    ffn
    syl
    ad3antrrr
    @11
    @6
    @14
    c0
    @11
    @4
    cX
    vw
    cv
    #
    wcel
    #
    @18
    cF
    cfv
    #
    @18
    cG
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
    cX
    @3
    wcel
    #
    @6
    @14
    wceq
    #
    @15
    wph
    @24
    @1
    @4
    @10
    wph
    cX
    cB
    wcel
    #
    cX
    cF
    cfv
    cX
    cG
    cfv
    wcel
    #
    @24
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
    simp3d
    ad3antrrr
    @11
    cX
    @8
    wss
    #
    @9
    @25
    @2
    @30
    @4
    @10
    wph
    vx
    vy
    vz
    vw
    vu
    cA
    cB
    cS
    cT
    cF
    cG
    cO
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
    cantnflem1.o
    cantnflem1b
    ad2antrr
    @5
    @7
    @9
    simprr
    @11
    cX
    con0
    wcel
    #
    @3
    con0
    wcel
    #
    @30
    @9
    wa
    @25
    wi
    wph
    @31
    @1
    @4
    @10
    wph
    @12
    @27
    @31
    cantnfs.b
    wph
    @27
    @28
    @24
    @29
    simp1d
    cB
    cX
    onelon
    syl2anc
    ad3antrrr
    @5
    @32
    @10
    wph
    @4
    @32
    @1
    wph
    cB
    con0
    @3
    wph
    @12
    cB
    con0
    wss
    cantnfs.b
    cB
    onss
    syl
    sselda
    adantlr
    adantr
    cX
    @8
    @3
    ontr2
    syl2anc
    mp2and
    @23
    @25
    @26
    wi
    vw
    @3
    cB
    @18
    @3
    wceq
    #
    @19
    @25
    @22
    @26
    @18
    @3
    cX
    eleq2
    @33
    @20
    @6
    @21
    @14
    @18
    @3
    cF
    fveq2
    @18
    @3
    cG
    fveq2
    eqeq12d
    imbi12d
    rspcv
    syl3c
    @5
    @7
    @9
    simprl
    eqnetrrd
    cB
    cG
    con0
    @3
    fvn0elsupp
    syl22anc
end
