include "com.mm"
include "wcel.mm"
include "wa.mm"
include "csuc.mm"
include "cfv.mm"
include "cvv.mm"
include "cv.mm"
include "coe.mm"
include "co.mm"
include "comu.mm"
include "coa.mm"
include "cmpt2.mm"
include "wceq.mm"
include "c0.mm"
include "seqomsuc.mm"
include "adantl.mm"
include "elex.mm"
include "fvex.mm"
include "simpl.mm"
include "fveq2d.mm"
include "oveq2d.mm"
include "oveq12d.mm"
include "simpr.mm"
include "fveq2.mm"
include "oveq1d.mm"
include "oveq2.mm"
include "cbvmpt2v.mm"
include "ovex.mm"
include "ovmpt2a.mm"
include "sylancl.mm"
include "eqtrd.mm"

theorem cantnfsuc
  let wph: wff ph
  let vz: setvar z
  let cA: class A
  let cB: class B
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
  let cC: class C
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

  disjoint k z
  disjoint B k
  disjoint B z
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
  assert |- ( ( ph /\ K e. _om ) -> ( H ` suc K ) = ( ( ( A ^o ( G ` K ) ) .o ( F ` ( G ` K ) ) ) +o ( H ` K ) ) )

  proof
    wph
    cK
    com
    wcel
    #
    wa
    #
    cK
    csuc
    cH
    cfv
    #
    cK
    cK
    cH
    cfv
    #
    vk
    vz
    cvv
    cvv
    cA
    vk
    cv
    #
    cG
    cfv
    #
    coe
    co
    #
    @5
    cF
    cfv
    #
    comu
    co
    #
    vz
    cv
    #
    coa
    co
    #
    cmpt2
    #
    co
    #
    cA
    cK
    cG
    cfv
    #
    coe
    co
    #
    @13
    cF
    cfv
    #
    comu
    co
    #
    @3
    coa
    co
    #
    @0
    @2
    @12
    wceq
    wph
    cK
    @11
    cH
    c0
    cantnfval.h
    seqomsuc
    adantl
    @1
    cK
    cvv
    wcel
    #
    @3
    cvv
    wcel
    @12
    @17
    wceq
    @0
    @18
    wph
    cK
    com
    elex
    adantl
    cK
    cH
    fvex
    vu
    vv
    cK
    @3
    cvv
    cvv
    cA
    vu
    cv
    #
    cG
    cfv
    #
    coe
    co
    #
    @20
    cF
    cfv
    #
    comu
    co
    #
    vv
    cv
    #
    coa
    co
    #
    @17
    @11
    @19
    cK
    wceq
    #
    @24
    @3
    wceq
    #
    wa
    #
    @23
    @16
    @24
    @3
    coa
    @28
    @21
    @14
    @22
    @15
    comu
    @28
    @20
    @13
    cA
    coe
    @28
    @19
    cK
    cG
    @26
    @27
    simpl
    fveq2d
    #
    oveq2d
    @28
    @20
    @13
    cF
    @29
    fveq2d
    oveq12d
    @26
    @27
    simpr
    oveq12d
    vk
    vz
    vu
    vv
    cvv
    cvv
    @10
    @25
    @23
    @9
    coa
    co
    @4
    @19
    wceq
    #
    @8
    @23
    @9
    coa
    @30
    @6
    @21
    @7
    @22
    comu
    @30
    @5
    @20
    cA
    coe
    @4
    @19
    cG
    fveq2
    #
    oveq2d
    @30
    @5
    @20
    cF
    @31
    fveq2d
    oveq12d
    oveq1d
    @9
    @24
    @23
    coa
    oveq2
    cbvmpt2v
    @16
    @3
    coa
    ovex
    ovmpt2a
    sylancl
    eqtrd
end
