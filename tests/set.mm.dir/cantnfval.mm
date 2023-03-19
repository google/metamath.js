include "ccnf.mm"
include "co.mm"
include "cfv.mm"
include "cv.mm"
include "c0.mm"
include "cfsupp.mm"
include "wbr.mm"
include "cmap.mm"
include "crab.mm"
include "csupp.mm"
include "cep.mm"
include "coi.mm"
include "cdm.mm"
include "cvv.mm"
include "coe.mm"
include "comu.mm"
include "coa.mm"
include "cmpt2.mm"
include "cseqom.mm"
include "csb.mm"
include "cmpt.mm"
include "eqid.mm"
include "cantnffval.mm"
include "fveq1d.mm"
include "wcel.mm"
include "wceq.mm"
include "cantnfdm.mm"
include "syl5eq.mm"
include "eleqtrd.mm"
include "ovex.mm"
include "oiexg.mm"
include "mp1i.mm"
include "wa.mm"
include "simpr.mm"
include "oveq1.mm"
include "adantr.mm"
include "oieq2.mm"
include "syl.mm"
include "eqtrd.mm"
include "syl6eqr.mm"
include "oveq2d.mm"
include "simpl.mm"
include "fveq12d.mm"
include "oveq12d.mm"
include "oveq1d.mm"
include "mpt2eq3dv.mm"
include "seqomeq12.mm"
include "sylancl.mm"
include "dmeqd.mm"
include "csbied.mm"
include "fvex.mm"
include "fvmpt.mm"

theorem cantnfval
  let wph: wff ph
  let vz: setvar z
  let cA: class A
  let cB: class B
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
  let cC: class C
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
  assert |- ( ph -> ( ( A CNF B ) ` F ) = ( H ` dom G ) )

  proof
    wph
    cF
    cA
    cB
    ccnf
    co
    #
    cfv
    cF
    vf
    vg
    cv
    c0
    cfsupp
    wbr
    vg
    cA
    cB
    cmap
    co
    crab
    #
    vh
    vf
    cv
    #
    c0
    csupp
    co
    #
    cep
    coi
    #
    vh
    cv
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
    @5
    cfv
    #
    coe
    co
    #
    @8
    @2
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
    c0
    cseqom
    #
    cfv
    #
    csb
    #
    cmpt
    #
    cfv
    #
    cG
    cdm
    #
    cH
    cfv
    #
    wph
    cF
    @0
    @18
    wph
    vz
    cA
    cB
    @1
    vf
    vg
    vh
    vk
    @1
    eqid
    #
    cantnfs.a
    cantnfs.b
    cantnffval
    fveq1d
    wph
    cF
    @1
    wcel
    @19
    @21
    wceq
    wph
    cF
    cS
    @1
    cantnfcl.f
    wph
    cS
    @0
    cdm
    @1
    cantnfs.s
    wph
    cA
    cB
    @1
    vg
    @22
    cantnfs.a
    cantnfs.b
    cantnfdm
    syl5eq
    eleqtrd
    vf
    cF
    @17
    @21
    @1
    @18
    @2
    cF
    wceq
    #
    vh
    @4
    @16
    @21
    cvv
    @3
    cvv
    wcel
    @4
    cvv
    wcel
    @23
    @2
    c0
    csupp
    ovex
    @3
    cep
    @4
    cvv
    @4
    eqid
    oiexg
    mp1i
    @23
    @5
    @4
    wceq
    #
    wa
    #
    @6
    @20
    @15
    cH
    @25
    @15
    vk
    vz
    cvv
    cvv
    cA
    @7
    cG
    cfv
    #
    coe
    co
    #
    @26
    cF
    cfv
    #
    comu
    co
    #
    @12
    coa
    co
    #
    cmpt2
    #
    c0
    cseqom
    #
    cH
    @25
    @14
    @31
    wceq
    c0
    c0
    wceq
    @15
    @32
    wceq
    @25
    vk
    vz
    cvv
    cvv
    @13
    @30
    @25
    @11
    @29
    @12
    coa
    @25
    @9
    @27
    @10
    @28
    comu
    @25
    @8
    @26
    cA
    coe
    @25
    @7
    @5
    cG
    @25
    @5
    cF
    c0
    csupp
    co
    #
    cep
    coi
    #
    cG
    @25
    @5
    @4
    @34
    @23
    @24
    simpr
    @25
    @3
    @33
    wceq
    #
    @4
    @34
    wceq
    @23
    @35
    @24
    @2
    cF
    c0
    csupp
    oveq1
    adantr
    @3
    @33
    cep
    oieq2
    syl
    eqtrd
    cantnfcl.g
    syl6eqr
    #
    fveq1d
    #
    oveq2d
    @25
    @8
    @26
    @2
    cF
    @23
    @24
    simpl
    @37
    fveq12d
    oveq12d
    oveq1d
    mpt2eq3dv
    c0
    eqid
    @14
    @31
    c0
    c0
    seqomeq12
    sylancl
    cantnfval.h
    syl6eqr
    @25
    @5
    cG
    @36
    dmeqd
    fveq12d
    csbied
    @18
    eqid
    @20
    cH
    fvex
    fvmpt
    syl
    eqtrd
end
